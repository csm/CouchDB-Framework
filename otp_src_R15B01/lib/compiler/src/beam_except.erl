%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2011. All Rights Reserved.
%%
%% The contents of this file are subject to the Erlang Public License,
%% Version 1.1, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Erlang Public License along with this software. If not, it can be
%% retrieved online at http://www.erlang.org/.
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
%%
%% %CopyrightEnd%
%%

-module(beam_except).
-export([module/2]).

%%% Rewrite certain calls to erlang:error/{1,2} to specialized
%%% instructions:
%%%
%%% erlang:error({badmatch,Value})       => badmatch Value
%%% erlang:error({case_clause,Value})    => case_end Value
%%% erlang:error({try_clause,Value})     => try_case_end Value
%%% erlang:error(if_clause)              => if_end
%%% erlang:error(function_clause, Args)  => jump FuncInfoLabel
%%%

-import(lists, [reverse/1]).

module({Mod,Exp,Attr,Fs0,Lc}, _Opt) ->
    Fs = [function(F) || F <- Fs0],
    {ok,{Mod,Exp,Attr,Fs,Lc}}.

function({function,Name,Arity,CLabel,Is0}) ->
    try
	Is = function_1(Is0),
	{function,Name,Arity,CLabel,Is}
    catch
	Class:Error ->
	    Stack = erlang:get_stacktrace(),
	    io:fwrite("Function: ~w/~w\n", [Name,Arity]),
	    erlang:raise(Class, Error, Stack)
    end.

-record(st,
	{lbl,					%func_info label
	 loc					%location for func_info
	 }).

function_1(Is0) ->
    case Is0 of
	[{label,Lbl},{line,Loc}|_] ->
	    St = #st{lbl=Lbl,loc=Loc},
	    translate(Is0, St, []);
	[{label,_}|_] ->
	    %% No line numbers. The source must be a .S file.
	    %% There is no need to do anything.
	    Is0
    end.

translate([{call_ext,Ar,{extfunc,erlang,error,Ar}}=I|Is], St, Acc) ->
    translate_1(Ar, I, Is, St, Acc);
translate([{call_ext_only,Ar,{extfunc,erlang,error,Ar}}=I|Is], St, Acc) ->
    translate_1(Ar, I, Is, St, Acc);
translate([{call_ext_last,Ar,{extfunc,erlang,error,Ar},_}=I|Is], St, Acc) ->
    translate_1(Ar, I, Is, St, Acc);
translate([I|Is], St, Acc) ->
    translate(Is, St, [I|Acc]);
translate([], _, Acc) ->
    reverse(Acc).

translate_1(Ar, I, Is, St, [{line,_}=Line|Acc1]=Acc0) ->
    case dig_out(Ar, Acc1) of
	no ->
	    translate(Is, St, [I|Acc0]);
	{yes,function_clause,Acc2} ->
	    case {Line,St} of
		{{line,Loc},#st{lbl=Fi,loc=Loc}} ->
		    Instr = {jump,{f,Fi}},
		    translate(Is, St, [Instr|Acc2]);
		{_,_} ->
		    %% This must be "error(function_clause, Args)" in
		    %% the Erlang source code. Don't translate.
		    translate(Is, St, [I|Acc0])
	    end;
	{yes,Instr,Acc2} ->
	    translate(Is, St, [Instr,Line|Acc2])
    end.

dig_out(Ar, [{kill,_}|Is]) ->
    dig_out(Ar, Is);
dig_out(1, [{block,Bl0}|Is]) ->
    case dig_out_block(reverse(Bl0)) of
	no -> no;
	{yes,What,[]} ->
	    {yes,What,Is};
	{yes,What,Bl} ->
	    {yes,What,[{block,Bl}|Is]}
    end;
dig_out(2, [{block,Bl}|Is]) ->
    case dig_out_block_fc(Bl) of
	no -> no;
	{yes,What} -> {yes,What,Is}
    end;
dig_out(_, _) -> no.

dig_out_block([{set,[{x,0}],[{atom,if_clause}],move}]) ->
    {yes,if_end,[]};
dig_out_block([{set,[{x,0}],[{literal,{Exc,Value}}],move}|Is]) ->
    translate_exception(Exc, {literal,Value}, Is, 0);
dig_out_block([{set,[{x,0}],[Tuple],move},
	       {set,[],[Value],put},
	       {set,[],[{atom,Exc}],put},
	       {set,[Tuple],[],{put_tuple,2}}|Is]) ->
    translate_exception(Exc, Value, Is, 3);
dig_out_block([{set,[],[Value],put},
	       {set,[],[{atom,Exc}],put},
	       {set,[{x,0}],[],{put_tuple,2}}|Is]) ->
    translate_exception(Exc, Value, Is, 3);
dig_out_block(_) -> no.

translate_exception(badmatch, Val, Is, Words) ->
    {yes,{badmatch,Val},fix_block(Is, Words)};
translate_exception(case_clause, Val, Is, Words) ->
    {yes,{case_end,Val},fix_block(Is, Words)};
translate_exception(try_clause, Val, Is, Words) ->
    {yes,{try_case_end,Val},fix_block(Is, Words)};
translate_exception(_, _, _, _) -> no.

fix_block(Is, 0) ->
    reverse(Is);
fix_block(Is0, Words) ->
    [{set,[],[],{alloc,Live,{F1,F2,Needed,F3}}}|Is] = reverse(Is0),
    [{set,[],[],{alloc,Live,{F1,F2,Needed-Words,F3}}}|Is].

dig_out_block_fc([{set,[],[],{alloc,Live,_}}|Bl]) ->
    dig_out_fc(Bl, Live-1, nil);
dig_out_block_fc(_) -> no.

dig_out_fc([{set,[Dst],[{x,Reg},Dst0],put_list}|Is], Reg, Dst0) ->
    dig_out_fc(Is, Reg-1, Dst);
dig_out_fc([{set,[{x,0}],[{atom,function_clause}],move}], -1, {x,1}) ->
    {yes,function_clause};
dig_out_fc(_, _, _) -> no.

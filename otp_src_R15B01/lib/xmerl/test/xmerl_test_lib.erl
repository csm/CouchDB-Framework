%%
%% %CopyrightBegin%
%% 
%% Copyright Ericsson AB 2006-2011. All Rights Reserved.
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
%%%-------------------------------------------------------------------
%%% File    : xmerl_test_lib.erl
%%% Author  : Bertil Karlsson <bertil@finrod>
%%% Description : 
%%%
%%% Created : 28 Apr 2006 by Bertil Karlsson <bertil@finrod>
%%%-------------------------------------------------------------------
-module(xmerl_test_lib).

-compile(export_all).

-include_lib("test_server/include/test_server.hrl").
-include_lib("xmerl/include/xmerl.hrl").

%% cmp_element/2
%% First argument result after parsing
%% Second argument result after validation
cmp_element(E,E) ->
    ok;
cmp_element(#xmlElement{name=N,attributes=A1,content=C1},
	    #xmlElement{name=N,attributes=A2,content=C2}) ->
    case cmp_attributes(A1,A2) of
	ok ->
	    cmp_elements(C1,C2);
	Err -> Err
    end;
cmp_element(#xmlText{},#xmlText{}) ->
    ok;
cmp_element(A,B) ->
    {error,{A,does_not_match,B}}.

cmp_elements([H1|T1],[H2|T2]) ->
    case cmp_element(H1,H2) of
	ok ->
	    cmp_elements(T1,T2);
	Err ->
	    Err
    end;
cmp_elements([],[]) ->
    ok.

%% All attributes in argument 1 must be present in 2
cmp_attributes([A1|T1],Atts2) ->
    case keysearch_delete(A1#xmlAttribute.name,#xmlAttribute.name,Atts2) of
	{A2,NewAtts2} ->
	    case A1#xmlAttribute.value == A2#xmlAttribute.value of
		true ->
		    cmp_attributes(T1,NewAtts2);
		_ ->
		    {error,{mismatching_values_in_attsibutes,A1,A2}}
	    end;
	_ ->
	    {error,{no_matching_attsibute,A1,in,Atts2}}
    end;
cmp_attributes([],_) ->
   ok.

keysearch_delete(Key,N,List) ->
    case lists:keysearch(Key,N,List) of
	{value,Res} ->
	    {Res,lists:keydelete(Key,N,List)};
	_ ->
	    false
    end.


%% Some test suites use the same testdata ("xmerl_sax_std_SUITE" and "xmerl_std_SUITE"),
%% so the data directory is not cloned. This function retrieves the path to
%% the original data directory.

get_data_dir(Config) ->
    Data = ?config(data_dir, Config),
    Opts = [{return,list}],
    re:replace(Data, "xmerl_sax_std_SUITE", "xmerl_std_SUITE", Opts).

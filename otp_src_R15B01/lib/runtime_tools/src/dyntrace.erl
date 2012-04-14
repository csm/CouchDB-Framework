-module(dyntrace).

%%% @doc The Dynamic tracing interface module
%%%
%%% This Dynamic tracing interface module, with the corresponding NIFs, should
%%% work on any operating system platform where user-space DTrace/Systemtap 
%%% (and in the future LttNG UST) probes are supported.
%%%
%%% Use the `dyntrace:init()' function to load the NIF shared library and
%%% to initialize library's private state.
%%%
%%% It is recommended that you use the `dyntrace:p()' function to add
%%% Dynamic trace probes to your Erlang code.  This function can accept up to
%%% four integer arguments and four string arguments; the integer
%%% argument(s) must come before any string argument.  For example:
%%% ```
%%% 1> dyntrace:put_tag("GGOOOAAALL!!!!!").
%%% true
%%% 2> dyntrace:init().
%%% ok
%%%
%%% % % % If using dtrace, enable the Dynamic trace probe using the 'dtrace' 
%%% % % % command.
%%%
%%% 3> dyntrace:p(7, 8, 9, "one", "four").
%%% true
%%% '''
%%%
%%% Output from the example D script `user-probe.d' looks like:
%%% ```
%%% <0.34.0> GGOOOAAALL!!!!! 7 8 9 0 'one' 'four' '' ''
%%% '''
%%%
%%% If the expected type of variable is not present, e.g. integer when
%%% integer() is expected, or an I/O list when iolist() is expected,
%%% then the driver will ignore the user's input and use a default
%%% value of 0 or NULL, respectively.

-export([available/0,
         user_trace_s1/1, % TODO: unify with pid & tag args like user_trace_i4s4
         p/0, p/1, p/2, p/3, p/4, p/5, p/6, p/7, p/8]).
-export([put_tag/1, get_tag/0, get_tag_data/0, spread_tag/1, restore_tag/1]).

-export([scaff/0]). % Development only
-export([user_trace_i4s4/9]). % Know what you're doing!
-on_load(on_load/0).

-type probe_arg() :: integer() | iolist().
-type int_p_arg() :: integer() | iolist() | undef.

%% The *_maybe() types use atom() instead of a stricter 'undef'
%% because user_trace_i4s4/9 is exposed to the outside world, and
%% because the driver will allow any atom to be used as a "not
%% present" indication, we'll allow any atom in the types.

-type integer_maybe() :: integer() | atom().
-type iolist_maybe() :: iolist() | atom().

on_load() ->
    PrivDir = code:priv_dir(runtime_tools),
    LibName = "dyntrace",
    Lib = filename:join([PrivDir, "lib", LibName]),
    Status = case erlang:load_nif(Lib, 0) of
                 ok -> ok;
                 {error, {load_failed, _}}=Error1 ->
                     ArchLibDir = 
                         filename:join([PrivDir, "lib", 
                                        erlang:system_info(system_architecture)]),
                     Candidate =
                         filelib:wildcard(filename:join([ArchLibDir,LibName ++ "*" ])),
                     case Candidate of
                         [] -> Error1;
                         _ ->
                             ArchLib = filename:join([ArchLibDir, LibName]),
                             erlang:load_nif(ArchLib, 0)
                     end;
                 Error1 -> Error1
             end,
    case Status of
        ok -> ok;
        {error, {E, Str}} ->
	    case erlang:system_info(dynamic_trace) of
		none ->
		    ok;
		_ ->
		    error_logger:error_msg("Unable to load dyntrace library. Failed with error:~n
\"~p, ~s\"~n"
					   "Dynamic tracing is enabled but the driver is not built correctly~n",[
														 E,Str]),
		    Status
	    end
    end.

%%%
%%% NIF placeholders
%%%

-spec available() -> true | false.

available() ->
    erlang:nif_error(nif_not_loaded).

-spec user_trace_s1(iolist()) -> true | false | error | badarg.

user_trace_s1(_Message) ->
    erlang:nif_error(nif_not_loaded).

-spec user_trace_i4s4(iolist(),
                      integer_maybe(), integer_maybe(),
                          integer_maybe(), integer_maybe(),
                      iolist_maybe(), iolist_maybe(),
                          iolist_maybe(), iolist_maybe()) ->
      true | false | error | badarg.

user_trace_i4s4(_, _, _, _, _, _, _, _, _) ->
    erlang:nif_error(nif_not_loaded).

%%%
%%% Erlang support functions
%%%

-spec p() -> true | false | error | badarg.

p() ->
    user_trace_int(undef, undef, undef, undef, undef, undef, undef, undef).

-spec p(probe_arg()) -> true | false | error | badarg.

p(I1) when is_integer(I1) ->
    user_trace_int(I1, undef, undef, undef, undef, undef, undef, undef);
p(S1) ->
    user_trace_int(undef, undef, undef, undef, S1, undef, undef, undef).

-spec p(probe_arg(), probe_arg()) -> true | false | error | badarg.

p(I1, I2) when is_integer(I1), is_integer(I2) ->
    user_trace_int(I1, I2, undef, undef, undef, undef, undef, undef);
p(I1, S1) when is_integer(I1) ->
    user_trace_int(I1, undef, undef, undef, S1, undef, undef, undef);
p(S1, S2) ->
    user_trace_int(undef, undef, undef, undef, S1, S2, undef, undef).

-spec p(probe_arg(), probe_arg(), probe_arg()) -> true | false | error | badarg.

p(I1, I2, I3) when is_integer(I1), is_integer(I2), is_integer(I3) ->
    user_trace_int(I1, I2, I3, undef, undef, undef, undef, undef);
p(I1, I2, S1) when is_integer(I1), is_integer(I2) ->
    user_trace_int(I1, I2, undef, undef, S1, undef, undef, undef);
p(I1, S1, S2) when is_integer(I1) ->
    user_trace_int(I1, undef, undef, undef, S1, S2, undef, undef);
p(S1, S2, S3) ->
    user_trace_int(undef, undef, undef, undef, S1, S2, S3, undef).

-spec p(probe_arg(), probe_arg(), probe_arg(), probe_arg()) ->
      true | false | error | badarg.

p(I1, I2, I3, I4) when is_integer(I1), is_integer(I2), is_integer(I3), is_integer(I4) ->
    user_trace_int(I1, I2, I3, I4, undef, undef, undef, undef);
p(I1, I2, I3, S1) when is_integer(I1), is_integer(I2), is_integer(I3) ->
    user_trace_int(I1, I2, I3, undef, S1, undef, undef, undef);
p(I1, I2, S1, S2) when is_integer(I1), is_integer(I2) ->
    user_trace_int(I1, I2, undef, undef, S1, S2, undef, undef);
p(I1, S1, S2, S3) when is_integer(I1) ->
    user_trace_int(I1, undef, undef, undef, S1, S2, S3, undef);
p(S1, S2, S3, S4) ->
    user_trace_int(undef, undef, undef, undef, S1, S2, S3, S4).

-spec p(probe_arg(), probe_arg(), probe_arg(), probe_arg(),
        probe_arg()) ->
      true | false | error | badarg.

p(I1, I2, I3, I4, S1) when is_integer(I1), is_integer(I2), is_integer(I3), is_integer(I4) ->
    user_trace_int(I1, I2, I3, I4, S1, undef, undef, undef);
p(I1, I2, I3, S1, S2) when is_integer(I1), is_integer(I2), is_integer(I3) ->
    user_trace_int(I1, I2, I3, undef, S1, S2, undef, undef);
p(I1, I2, S1, S2, S3) when is_integer(I1), is_integer(I2) ->
    user_trace_int(I1, I2, undef, undef, S1, S2, S3, undef);
p(I1, S1, S2, S3, S4) when is_integer(I1) ->
    user_trace_int(I1, undef, undef, undef, S1, S2, S3, S4).

-spec p(probe_arg(), probe_arg(), probe_arg(), probe_arg(),
        probe_arg(), probe_arg()) ->
      true | false | error | badarg.

p(I1, I2, I3, I4, S1, S2) when is_integer(I1), is_integer(I2), is_integer(I3), is_integer(I4) ->
    user_trace_int(I1, I2, I3, I4, S1, S2, undef, undef);
p(I1, I2, I3, S1, S2, S3) when is_integer(I1), is_integer(I2), is_integer(I3) ->
    user_trace_int(I1, I2, I3, undef, S1, S2, S3, undef);
p(I1, I2, S1, S2, S3, S4) when is_integer(I1), is_integer(I2) ->
    user_trace_int(I1, I2, undef, undef, S1, S2, S3, S4).

-spec p(probe_arg(), probe_arg(), probe_arg(), probe_arg(),
        probe_arg(), probe_arg(), probe_arg()) ->
      true | false | error | badarg.

p(I1, I2, I3, I4, S1, S2, S3) when is_integer(I1), is_integer(I2), is_integer(I3), is_integer(I4) ->
    user_trace_int(I1, I2, I3, I4, S1, S2, S3, undef);
p(I1, I2, I3, S1, S2, S3, S4) when is_integer(I1), is_integer(I2), is_integer(I3) ->
    user_trace_int(I1, I2, I3, undef, S1, S2, S3, S4).

-spec p(probe_arg(), probe_arg(), probe_arg(), probe_arg(),
        probe_arg(), probe_arg(), probe_arg(), probe_arg()) ->
      true | false | error | badarg.

p(I1, I2, I3, I4, S1, S2, S3, S4) when is_integer(I1), is_integer(I2), is_integer(I3), is_integer(I4) ->
    user_trace_int(I1, I2, I3, I4, S1, S2, S3, S4).

-spec user_trace_int(int_p_arg(), int_p_arg(), int_p_arg(), int_p_arg(),
                     int_p_arg(), int_p_arg(), int_p_arg(), int_p_arg()) ->
      true | false | error | badarg.

user_trace_int(I1, I2, I3, I4, S1, S2, S3, S4) ->
    UTag = get_tag(),
    try
        user_trace_i4s4(UTag, I1, I2, I3, I4, S1, S2, S3, S4)
    catch
        error:nif_not_loaded ->
            false
    end.

-spec put_tag(undefined | iodata()) -> binary() | undefined.
put_tag(Data) ->
    erlang:dt_put_tag(unicode:characters_to_binary(Data)).

-spec get_tag() -> binary() | undefined.
get_tag() ->
    erlang:dt_get_tag().

-spec get_tag_data() -> binary() | undefined.
%% Gets tag if set, otherwise the spread tag data from last incoming message
get_tag_data() ->
    erlang:dt_get_tag_data().

-spec spread_tag(boolean()) -> true | {non_neg_integer(), binary() | []}.
%% Makes the tag behave as a sequential trace token, will spread with 
%% messages to be picked up by someone using get_tag_data 
spread_tag(B) ->			   
    erlang:dt_spread_tag(B).

-spec restore_tag(true | {non_neg_integer(), binary() | []}) -> true.
restore_tag(T) ->
    erlang:dt_restore_tag(T).
    

%% Scaffolding to write tedious code: quick brute force and not 100% correct.

scaff_int_args(N) ->
    L = lists:sublist(["I1", "I2", "I3", "I4"], N),
    [string:join(L, ", ")].

scaff_int_guards(N) ->
    L = lists:sublist(["is_integer(I1)", "is_integer(I2)", "is_integer(I3)",
                       "is_integer(I4)"], N),
    lists:flatten(string:join(L, ", ")).

scaff_char_args(N) ->
    L = lists:sublist(["S1", "S2", "S3", "S4"], N),
    [string:join(L, ", ")].

scaff_fill(N) ->
    [string:join(lists:duplicate(N, "undef"), ", ")].

scaff() ->
    L = [begin
             IntArgs = scaff_int_args(N_int),
             IntGuards = scaff_int_guards(N_int),
             IntFill = scaff_fill(4 - N_int),
             CharArgs = scaff_char_args(N_char),
             CharFill = scaff_fill(4 - N_char),
             InArgs = string:join(IntArgs ++ CharArgs, ", "),
             OutArgs = string:join(IntArgs ++ IntFill ++ CharArgs ++ CharFill,
                                   ", "),
             {N_int + N_char,
              lists:flatten([io_lib:format("p(~s) when ~s ->\n",
                                           [InArgs, IntGuards]),
                             io_lib:format("    user_trace_int(~s);\n", [OutArgs])
                            ])}
         end || N_int <- [0,1,2,3,4], N_char <- [0,1,2,3,4]],
    [io:format("%%~p\n~s", [N, Str]) || {N, Str} <- lists:sort(L)].

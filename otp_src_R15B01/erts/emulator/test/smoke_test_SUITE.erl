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

-module(smoke_test_SUITE).

-include_lib("test_server/include/test_server.hrl").

%-compile(export_all).
-export([all/0, suite/0,groups/0,init_per_suite/1, end_per_suite/1, 
	 init_per_group/2,end_per_group/2, 
	 init_per_testcase/2, end_per_testcase/2]).

-export([boot_combo/1]).

-define(DEFAULT_TIMEOUT, ?t:minutes(2)).

suite() -> [{ct_hooks,[ts_install_cth]}].

all() -> 
    [boot_combo].

groups() -> 
    [].

init_per_suite(Config) ->
    Config.

end_per_suite(_Config) ->
    ok.

init_per_group(_GroupName, Config) ->
    Config.

end_per_group(_GroupName, Config) ->
    Config.


init_per_testcase(Case, Config) when is_list(Config) ->
    Dog = ?t:timetrap(?DEFAULT_TIMEOUT),
    [{testcase, Case},{watchdog, Dog}|Config].

end_per_testcase(_Case, Config) when is_list(Config) ->
    Dog = ?config(watchdog, Config),
    ?t:timetrap_cancel(Dog),
    ok.

%%%
%%% The test cases -------------------------------------------------------------
%%%

boot_combo(Config) when is_list(Config) ->
    ZFlags = os:getenv("ERL_ZFLAGS"),
    NOOP = fun () -> ok end,
    A42 = fun () ->
		  case erlang:system_info(threads) of
		      true ->
			  42 = erlang:system_info(thread_pool_size);
		      false ->
			  ok
		  end
	  end,
    SMPDisable = fun () -> false = erlang:system_info(smp_support) end,
    try
	chk_boot(Config, "+Ktrue", NOOP),
	chk_boot(Config, "+A42", A42),
	chk_boot(Config, "-smp disable", SMPDisable),
	chk_boot(Config, "+Ktrue +A42", A42),
	chk_boot(Config, "-smp disable +A42",
		 fun () -> SMPDisable(), A42() end),
	chk_boot(Config, "-smp disable +Ktrue", SMPDisable),
	chk_boot(Config, "-smp disable +Ktrue +A42",
		 fun () -> SMPDisable(), A42() end),
	%% A lot more combos could be implemented...
	ok
    after
	os:putenv("ERL_ZFLAGS", case ZFlags of
				    false -> "";
				    _ -> ZFlags
				end)
    end.

%%%
%%% Aux functions --------------------------------------------------------------
%%%

chk_boot(Config, Args, Fun) ->
    true = os:putenv("ERL_ZFLAGS", Args),
    Success = make_ref(),
    Parent = self(),
    ?t:format("--- Testing ~s~n", [Args]),
    {ok, Node} = start_node(Config),
    Pid = spawn_link(Node, fun () ->
				   Fun(),
				   Parent ! {self(), Success}
			   end),
    receive
	{Pid, Success} ->
	    Node = node(Pid),
	    stop_node(Node),
	    ?t:format("--- Success!~n", []),
	    ok
    end.

start_node(Config) ->
    start_node(Config, "").

start_node(Config, Args) when is_list(Config) ->
    ?line Pa = filename:dirname(code:which(?MODULE)),
    ?line {A, B, C} = now(),
    ?line Name = list_to_atom(atom_to_list(?MODULE)
			      ++ "-"
			      ++ atom_to_list(?config(testcase, Config))
			      ++ "-"
			      ++ integer_to_list(A)
			      ++ "-"
			      ++ integer_to_list(B)
			      ++ "-"
			      ++ integer_to_list(C)),
    ?line ?t:start_node(Name, slave, [{args, "-pa "++Pa++" "++Args}]).

stop_node(Node) ->
    ?t:stop_node(Node).


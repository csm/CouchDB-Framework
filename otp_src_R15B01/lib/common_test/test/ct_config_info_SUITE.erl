%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2009-2011. All Rights Reserved.
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
%%% File: ct_config_info_SUITE
%%%
%%% Description: Test how Common Test handles info functions
%%% for the config functions.
%%%
%%%-------------------------------------------------------------------
-module(ct_config_info_SUITE).

-compile(export_all).

-include_lib("common_test/include/ct.hrl").
-include_lib("common_test/include/ct_event.hrl").

-define(eh, ct_test_support_eh).

%%--------------------------------------------------------------------
%% TEST SERVER CALLBACK FUNCTIONS
%%--------------------------------------------------------------------

%%--------------------------------------------------------------------
%% Description: Since Common Test starts another Test Server
%% instance, the tests need to be performed on a separate node (or
%% there will be clashes with logging processes etc).
%%--------------------------------------------------------------------
init_per_suite(Config) ->
    Config1 = ct_test_support:init_per_suite(Config),
    Config1.

end_per_suite(Config) ->
    ct_test_support:end_per_suite(Config).

init_per_testcase(TestCase, Config) ->
    ct_test_support:init_per_testcase(TestCase, Config).

end_per_testcase(TestCase, Config) ->
    ct_test_support:end_per_testcase(TestCase, Config).

suite() -> [{ct_hooks,[ts_install_cth]}].

all() -> 
    [
     config_info
    ].

%%--------------------------------------------------------------------
%% TEST CASES
%%--------------------------------------------------------------------

%%%-----------------------------------------------------------------
%%% 
config_info(Config) when is_list(Config) -> 
    DataDir = ?config(data_dir, Config),
    Suite = filename:join(DataDir, "config_info_1_SUITE"),
    {Opts,ERPid} = setup([{suite,Suite},
			  {label,config_info}], Config),
    ok = execute(config_info, Opts, ERPid, Config).

%%%-----------------------------------------------------------------
%%% HELP FUNCTIONS
%%%-----------------------------------------------------------------

setup(Test, Config) ->
    Opts0 = ct_test_support:get_opts(Config),
    Level = ?config(trace_level, Config),
    EvHArgs = [{cbm,ct_test_support},{trace_level,Level}],
    Opts = Opts0 ++ [{event_handler,{?eh,EvHArgs}}|Test],
    ERPid = ct_test_support:start_event_receiver(Config),
    {Opts,ERPid}.

execute(Name, Opts, ERPid, Config) ->
    ok = ct_test_support:run(Opts, Config),
    Events = ct_test_support:get_events(ERPid, Config),

    ct_test_support:log_events(Name, 
			       reformat(Events, ?eh),
			       ?config(priv_dir, Config),
			       Opts),

    TestEvents = events_to_check(Name),
    ct_test_support:verify_events(TestEvents, Events, Config).

reformat(Events, EH) ->
    ct_test_support:reformat(Events, EH).

%%%-----------------------------------------------------------------
%%% TEST EVENTS
%%%-----------------------------------------------------------------
events_to_check(Test) ->
    %% 2 tests (ct:run_test + script_start) is default
    events_to_check(Test, 2).

events_to_check(_, 0) ->
    [];
events_to_check(Test, N) ->
    test_events(Test) ++ events_to_check(Test, N-1).


test_events(config_info) ->
    [
     {?eh,start_logging,{'DEF','RUNDIR'}},
     {?eh,test_start,{'DEF',{'START_TIME','LOGDIR'}}},
     {?eh,start_info,{1,1,6}},
     {?eh,tc_done,{config_info_1_SUITE,init_per_suite,ok}},

     [{?eh,tc_start,{config_info_1_SUITE,{init_per_group,g1,[]}}},
      {?eh,tc_done,{config_info_1_SUITE,
		    {init_per_group,unknown,[]},
		    {failed,{timetrap_timeout,350}}}},
      {?eh,tc_auto_skip,{config_info_1_SUITE,t11,
	{failed,{config_info_1_SUITE,init_per_group,{timetrap_timeout,350}}}}},
      {?eh,tc_auto_skip,{config_info_1_SUITE,end_per_group,
			 {failed,{config_info_1_SUITE,init_per_group,
				  {timetrap_timeout,350}}}}}],

     [{?eh,tc_start,{config_info_1_SUITE,{init_per_group,g2,[]}}},
      {?eh,tc_done,{config_info_1_SUITE,{init_per_group,g2,[]},ok}},
      {?eh,tc_done,{config_info_1_SUITE,t21,ok}},
      {?eh,tc_start,{config_info_1_SUITE,{end_per_group,g2,[]}}},
      {?eh,tc_done,{config_info_1_SUITE,
		    {end_per_group,unknown,[]},
		    {failed,{timetrap_timeout,450}}}}],
     [{?eh,tc_start,{config_info_1_SUITE,{init_per_group,g3,[]}}},
      {?eh,tc_done,{config_info_1_SUITE,{init_per_group,g3,[]},ok}},
      [{?eh,tc_start,{config_info_1_SUITE,{init_per_group,g4,[]}}},
       {?eh,tc_done,{config_info_1_SUITE,
		     {init_per_group,unknown,[]},
		     {failed,{timetrap_timeout,400}}}},
       {?eh,tc_auto_skip,{config_info_1_SUITE,t41,
	 {failed,{config_info_1_SUITE,init_per_group,
		  {timetrap_timeout,400}}}}},
       {?eh,tc_auto_skip,{config_info_1_SUITE,end_per_group,
	 {failed,{config_info_1_SUITE,init_per_group,
		  {timetrap_timeout,400}}}}}],
      {?eh,tc_start,{config_info_1_SUITE,t31}},
      {?eh,tc_done,{config_info_1_SUITE,t31,
		    {skipped,{failed,{config_info_1_SUITE,init_per_testcase,
				      {timetrap_timeout,250}}}}}},
      {?eh,tc_start,{config_info_1_SUITE,t32}},
      {?eh,tc_done,{config_info_1_SUITE,t32,
		    {failed,{config_info_1_SUITE,end_per_testcase,
			     {timetrap_timeout,250}}}}},

      [{?eh,tc_start,{config_info_1_SUITE,{init_per_group,g5,[]}}},
       {?eh,tc_done,{config_info_1_SUITE,{init_per_group,g5,[]},ok}},
       {?eh,tc_done,{config_info_1_SUITE,t51,ok}},
       {?eh,tc_start,{config_info_1_SUITE,{end_per_group,g5,[]}}},
       {?eh,tc_done,{config_info_1_SUITE,
		     {end_per_group,unknown,[]},
		     {failed,{timetrap_timeout,400}}}}],
      {?eh,tc_start,{config_info_1_SUITE,{end_per_group,g3,[]}}},
      {?eh,tc_done,{config_info_1_SUITE,{end_per_group,g3,[]},ok}}],

     {?eh,tc_start,{config_info_1_SUITE,end_per_suite}},
     {?eh,tc_done,{config_info_1_SUITE,end_per_suite,
		   {failed,{timetrap_timeout,300}}}},
     {?eh,test_done,{'DEF','STOP_TIME'}},
     {?eh,stop_logging,[]}
    ].

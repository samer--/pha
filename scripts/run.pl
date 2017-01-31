#!/usr/bin/env swipl

:- use_module(library(dcg_core)).
:- use_module(library(dcg_shell)).
:- use_module(library(pha)).

file_search_path(pha,pack(pha/models)).

:- load(pha(alarm)).
:- run_belief(dcgshell).

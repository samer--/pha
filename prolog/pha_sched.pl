:- module(pha_sched, [nil_belief/1, cons_belief/3, explanation/2, prob/2]).

/** <module> PHA scheduler

This module uses the the PHA continuation capturing meta-interpreter in pha_mi.pl 
to run PHA goals and a priority queue to manage a collection of threads, each 
exploring a different possible world associated with a list of valuations of random 
variables. Each time a thread tries to sample a random variable, its continuation is
captured and a new set of threads corresponding to the different possible choices is 
created in a suspended state. next//1 then advances the state of the collection of 
threads by running all threads until a success is found or all threads fail.

A thread can either be a list of random variable valuations (assumptions) and a
continuation, or a continuation to be appended to a lazy list of explanations for
a previous goal. [cf. Monadic bind!]
*/

:- use_module(library(dcg_core)).
:- use_module(library(dcg_macros)).
:- use_module(library(typedef)).
:- use_module(library/priorityq, [pq_empty/1, pq_insert/4, pq_remove/4]).
:- use_module(pha_mi,    [glist/3, mi/3]).

:- type procq       == pair(prob,pq(thread)).
:- type explist     == llist(expentry).
:- type maybe(A)    ---> nothing ; just(A).
:- type explanation ---> ex(goal, assumptions).
:- type expentry    ---> refinement(weighted(explanation),maybe(prob)).
:- type thread      ---> tail(explist,cont)
                       ; thread(assumptions,cont).

% --------------- lazy list of explanations --------------------

nil_belief(Es) :- lazy:singleton(refinement(1:ex(true,[]),nothing), Es).
cons_belief(G, Es1, Es2) :- 
   glist(G, C, ans(G)), 
   proc_init(1, tail(Es1,C), PQ),
   unfold_search(PQ, Es2).

%% unfold_search(+P:prob, +PQ:procq, -Es:explist) is det.
%  Here, we lazily unfold a procq using next//1, with look-ahead to remaing queue probability.
unfold_search(Q1,E1) :- 
   next(X,Q1,Q2), !, Head=refinement(X,More), 
   (  proc_empty(Q2) -> More=nothing, lazy:singleton(Head, E1)
   ;  proc_total(Q2,QP), More=just(QP), lazy:cons(Head, pha_sched:unfold_search(Q2), E1)
   ).
unfold_search(_,E1) :- lazy:empty(E1).

%% explanation(+Es:explist, -E:weighted(explanation)) is nondet.
%  Unifies E with an explanation, finds other explanations on backtracking.
explanation(Es,E) :- lazy:member(refinement(E,_),Es).

%% prob(+Es:llist(expentry), -Ps:llist(interval(prob))) is det.
%  Compute a lazy stream of probability intervals from a lazy list of explanations.
prob(Es,Ps) :- prob1(Es,0,Ps). % freeze on Ps?

prob1(Es,P0,Ps) :-
   lazy:decons(Es, refinement(P:_,Rem), Es2), !,
   lazy:cons(range(P1,PMax), pha_sched:prob1(Es2,P1), Ps), 
   P1 is P0 + P, (Rem=just(R) -> PMax is P1+R; PMax=P1).
prob1(Es,P0,Ps) :-
   lazy:empty(Es),
   lazy:repeat(range(P0,P0), Ps).

% ------------------ process queue DCG ------------------------------

%% next(-E:weighted(explanation))// is semidet.
%  Gets the next explanation if there is one. 
%  Works in procq DCG.
next(X) --> proc_remove(P,Thread), run(Thread,P,X).

%% run(+T:thread,+P:prob,-E:weighted(explanation))// is semidet.
%  Runs a thread until it produces a request, or unfolds
%  an explanation tail and inserts any new explanations
%  as new threads. Works in procq DCG.
run(thread(AS,Cont),P,Y) --> 
   {mi(Cont,AS,Req)}, 
   respond(Req,AS,P,Y).
run(tail(E1,Cont),_,Y) --> 
   (  {lazy:head(E1, refinement(P:ex(_,AS),Rem))}
   -> proc_insert(P, thread(AS,Cont)),
      ({Rem=just(QP)} -> {lazy:tail(E1, ET)}, proc_insert(QP, tail(ET,Cont)); [])
   ),
   next(Y).

%% respond(+A:request, +AS:assumptions, +P:prob, -R:weighted(explanation))// is det.
%  Respond to request from mi/4, where AS is the list of assumptions made so far
%  and P is the probability associated with these choices.
respond(sus(TS), AS, P, Y) --> !, seqmap(suspend(AS,P),TS), next(Y).
respond(ret(G),  AS, P, P:ex(G,AS)) --> [].

%% suspend(+AS:assumptions, +P:prob, +T:susreq)// is det.
%  Adds a suspension request for probabilistic choice to priority queue of threads.
suspend(AS,P1,susreq(A,C,P)) --> { P2 is P1*P }, proc_insert(P2, thread([A|AS],C)).

proc_init(P,T,P-PQ1)          :- pq_empty(PQ0), pq_insert(P,T,PQ0,PQ1).
proc_insert(P,Th,T1-Q1,T2-Q2) :- pq_insert(P,Th,Q1,Q2), T2 is T1+P.
proc_remove(P,Th,T1-Q1,T2-Q2) :- pq_remove(P,Th,Q1,Q2), T2 is T1-P.
proc_empty(_-Q)               :- pq_empty(Q).
proc_total(T-_,T).


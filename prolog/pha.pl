:- module(pha, 
   [  run_belief/1
   ,  observe//1
   ,  unobserve//0
   ,  joint//1, joint//2
   ,  prob//2
   ,  explanation//1
   ,  explanations//1
   ,  explain//1
   ,  load/1
   ,  goals//0
   ,  edit//0
   ,  load//1
   ,  unobserve_all//0
   ]).

:- meta_predicate run_belief(//).

/** <module> Probabilistic Horn Abduction with random variables

   This is a more or less complete reimplementation of David Poole's
   probabilistic Horn abudction. 

   The mechanism for declaring and using random variables has been changed. Instead
   of using disjoint declarations in the PHA program file, you should use rv declarations,
   which look like this:
   ==
   rv( RVTerm, [ Prob1:Value1, Prob2:Value2, ...].
   ==
   Where RVTerm is an arbitrary term idenitfying the random variable, possibly
   using variables to stand for parameters of the random variable, and Value1, Value2 etc
   are arbitrary terms which can only contain variables that are in RVTerm. 
   You can also compute the distribution for an RV using an ordinary Prolog clause, eg
   ==
   rv( uniform(N), Dist) :- P is 1/N, findall(P:V, between(1,N,V), Dist).
   ==
   Then, to query an random variable, use
   ==
   RVTerm := Value
   ==
   RVTerm must be a ground term unifying with one of the random variables, and
   Value can be non-ground. This makes is much harder to go wrong with variables
   and use of functors in assumable hypotheses.

   ---++ Types

   In the following, =|rv(A)|= and =|head|= are not formally defined. Syntactically, they
   are abitrary terms. A term of type =|rv(A)|= denotes the name of random variable as found
   in the first argument of an rv/2 declartion and whose values are of type =|A|=. 
   Then, an =|assumption|= is an assertion about the value of a random variable, so
   ==
   assumption ---> rv(A) := A.
   ==
   A =|head|= is any term that is found in the head position in the rule database. 
   The type =|goal|= is a supertype of =|assumption|= 
   and =|head|= and can be defined syntactically by the following predicate:
   ==
   goal(X) :- rv(X,_); rule(X,_).
   goal((X,Y)) :- goal(X), goal(Y).
   goal(true).
   ==
   A program in the object language consists of a sequence of statements, where
   ==
   rv_head(A) ---> rv( rv(A), list(weighted(A))).
   statement ---> rv( rv(A), list(weighted(A)))
                ; (rv_head(A) :- prolog_body)
                ; (head :- goal)
                ; head.
   ==

   ---++ Usage
   To load a model, use =|load(FileSpec)|=, where Spec is a file specification using the SWI Prolog's
   file search path mechanism. An extension of 'pha' is assumed.

   To get an interactive shell to work with a model, you can use run_belief/1 with dcgshell as the
   command: this gives you a stateful top-level, where the state is managed by a DCG and the commands
   are interpreted as DCG goals. The DCG goal load//1 is available for loading models in the belief DCG.
   ==
   ?- use_module(library(dcg_shell)).
   ?- run_belief(dcgshell).
   user: call_dcg (dcg) >> load(pack(pha/models/alarm)).
   ==
   At this point, you can now declare observations in the form of PHA goals which are known to be true.
   The system computes the possible explanations for these observations and their probabilities.
   Observations are cumulative. For example:
   ==
   user: call_dcg (dcg) >> prob(fire(yes),P).
   user: call_dcg (dcg) >> prob(fire(yes)|smoke(yes),P).
   user: call_dcg (dcg) >> observe(alarm(yes)).
   user: call_dcg (dcg) >> prob(fire(yes),P).
   user: call_dcg (dcg) >> explain(fire(yes)).
   ==
*/

:- use_module(library(dcg_core)).
:- use_module(library(dcg_pair)).
:- use_module(library(dcg_macros)).
:- use_module(library(typedef)).
:- use_module(library(listutils), [cons/3]).
:- use_module(library(math), [add/3]).
:- use_module(pha_load, [load/1, edit//0]).
:- use_module(pha_sched, [nil_belief/1, cons_belief/3, explanation/2, prob/2]).
:- use_module(library/frozen,[]).

:- type stream(A)    ---> [A|stream(A)].
:- type interval(A)  ---> range(A,A).
:- type improving(A) ---> stream(interval(A)).
:- type tol(A)       ---> abs(A); rel(A).

% -------------------------------------------------------------------
% Belief state DCG: belief_stack == list(pair(goal,explist)).
% Each entry is a goal that has been observed to be true with a lazy
% list of explanations, each of which consists of a valuation of some
% random variables, a probability, and an estimate of the remaining
% unexplored probability mass.

help --> {print_help}.
print_help :- 
   maplist(command_help, 
           [ help -    "Print this help."
           , load(G) - "Load PHA program ~w"/[G]
           , observe(G) - "Add goal ~w to stack of observations"/[G]
           , unobserve  - "Remove most recently observed goal"
           , unobserve_all - "Remove all observed goals"
           , goals         - "Print all goals on observation stack"
           , prob(G,P)     - "Estimate probability ~w of goal ~w given current observations"/[P,G]
           , joint(P)      - "Estimate joint probability ~w of current observations"/[P]
           , joint(Tol,P ) - "Estimate joint probability ~w of current observations to within tolerance ~w"/[P,Tol] 
           , explanations(Eps) - "Print explanations of current observations up to missing prob ~w"/[Eps]
           , explanation(E) - "Find an explanation ~w of current goal stack, more on backtracking"/[E]
           , explain(G)     - "Print an explanation of goal ~w, more on backtracking"/[G]
           ]).

command_help(Cmd-Text) :-
   ( numbervars(Cmd-Text, 0, _),
     (Text = F/A -> format(string(T),F,A); T=Text),
     format('  ~p ~t~20|- ~s\n', [Cmd,T]),
     fail
   ; true
   ).

%% run_belief(+P:phrase(belief_stack)) is det.
%  Starts a DCG shell with an empty belief stack, then runs the
%  given DCG command.
run_belief(Cmd) :- nil_belief(E1), call_dcg(Cmd,[true-E1],_).

%% load(+F:FileSpec)// is det.
%  Clears old program, loads new one, and removes all observations.
load(F) --> {load(F)}, unobserve_all.

%% observe(+G:goal)// is det.
%  Adds a new observation.
observe(G) --> get([_-E1|_]), {cons_belief(G,E1,E2)}, cons(G-E2).

%% unobserve// is semidet.
%  Removes the last observation, fails if only nil belief is left.
unobserve --> \+get([_]), [_].

%% unobserve_all// is det.
%  Removes all observations.
unobserve_all --> unobserve -> unobserve_all; [].

%% goals// is det.
%  Prints all the observations on the stack, latest first.
goals --> get(ES), {maplist(print_goal,ES)}.
print_goal(G-_) :- writeln(G).

%% prob(+G:goal,-P:interval)// is det.
%  Computes the probabilty (to within default tolerance) of Goal given all observations, or if
%  Goal = G1 | G2, temporarily adds G2 as an observation before computing
%  the probability of G1.
prob(A|B,P) --> !, iso((observe(B),prob(A,P))).
prob(A,P) --> !, iso((prob_series(PP), observe(A),
                      prob_series(PA))),
              {  default_tolerance(Tol),
                 lazy:map(pha:cprob,PA,PP,V), 
                 approx(Tol,V,P)
              }.

cprob(range(P1,P2),range(_,Q2),range(R1,R2)) :- R1 is P1/Q2, R2 is P2/Q2.
prob_series(P) --> get([_-E|_]), {prob(E,P)}.

%% joint(+Tol:tolerance, -P:interval(prob))// is semidet.
%% joint(-P:interval(prob))// is semidet.
%  Computes an approximation to the joint probability of all the
%  observations so far.
joint(R) --> {default_tolerance(Tol)}, joint(Tol,R).
joint(Tol,R) --> prob_series(P), {approx(Tol,P,R)}.

%% explanations(+Epsilon:prob)// is det.
%  Prints enough explanations of the current observations to account
%  for all but Epsilon of the probability mass.
explanations(Eps) --> get([_-E|_]), {print_explanations(Eps,E)}.

%% explanation(-Ex:explanation)// is nondet.
%  Unifies Ex with an explanation for all observations, finds other
%  explanations on backtracking.
explanation(Ex) --> get([_-E|_]), {explanation(E,Ex)}.

%% explain(+G:goal)// is nondet.
%  Prints an explanation for G given the observations so far.
%  Produces other explanations on backtracking.
explain(G) --> iso((observe(G), explanation(E), {print_explanation(E)})).

% -------------------------------------------------------------------

print_explanations(Eps,E) :-
   accumex(Eps,E,(0-1)-Exps,(Tot-Rem)-[]),
   nl, maplist(print_explanation,Exps), nl,
   show('Total found probability',Tot),
   show(' Unexplored probability',Rem).

print_explanation(P:ex(G,AS)) :- nl,
   show('    Solution',G),
   show(' Explanation',AS),
   show(' Probability',P).

accumex(_,Es) --> {lazy:empty(Es)}, !, \< \> set(nothing).
accumex(Th,Es1) -->
   {lazy:head(Es1, refinement(P:Ex,Rem))},
   (add(P) <\> set(Rem)) <\> [P:Ex],
   ({Rem=just(R), R>Th} -> {lazy:tail(Es1, Es2)}, accumex(Th,Es2); []).


%% approx(+Tol:tol(A), +X:improving(A), -Y:interval(A)) is det.
%  Takes an improving value X (a lazy list of numeric intervals such that each is contained
%  within the previous) and finds the first interval Y that is small enough to satisfy the
%  absolute or relative tolerance specified by To.
approx(Tol,Rs,R) :- 
   lazy:head(Rs, R1),
   (  within_tolerance(Tol,R1) -> R=R1
   ;  lazy:tail(Rs,RT), approx(Tol,RT,R)
   ).

user:portray(F) :- float(F), format('~g',[F]).
user:portray(range(Min,Max)) :-
   Middle is (Min+Max)/2,
   Diff is (Max-Min)/2,
   format('~g ±~g',[Middle,Diff]).

default_tolerance(rel(0.001)).

within_tolerance(abs(Thresh),range(Min,Max)) :- Thresh>=Max-Min.
within_tolerance(rel(Thresh),range(Min,Max)) :- Thresh*(Max+Min)>=2*(Max-Min).

show(Label,Value) :- float(Value), !, format('~w: ~5f\n',[Label,Value]).
show(Label,Value) :- format('~w: ~w\n',[Label,Value]).


:- module(pha_mi, [glist//1, mi/3]).

/** <module> PHA meta-interpreter
*/

:- use_module(library(typedef)).

:- type goal  == term.
:- type rv(_) == term.
:- type prob == float.

:- type pair(A,B)   ---> A-B.
:- type weighted(A) ---> prob:A.
:- type assumption  ---> rv(A) := A.
:- type cont        ---> ans(term) ; [goal|cont].
:- type susreq      ---> susreq(assumption, cont, prob).  % suspend on probabilistic choice
:- type request     ---> sus(list(susreq)) % result of meta-interpretation is suspension
                       ; ret(goal).        % result of meta-interpreteation is a proven goal.

:- multifile pha_user:rule/3, pha_user:rv/2.

%% mi(+C:cont, +AS:list(assumption), -R:request) is det.
%  Runs the given continuation until either an answer is generated or
%  all threads of execution have become suspended on sampling decisions.
%  Essentially, this interpreter runs one intial thread as far as it can
%  without making any new assumptions, either reaching its goal or returning
%  a weighted set of new threads, each predicated on a new assumption.
mi(Cont, AS, R) :- mi(Cont, [], AS, [], R).

%% mi(+C:cont, +T1:list(cont), +AS:list(assumption), +TS:list(susreq), -R:request) is det.
mi(ans(G),_,_,_,ret(G)). 
mi([H|G1],T1,AS,TS,R) :- mi1(H,G1,T1,AS,TS,R) -> true; mi2(T1,AS,TS,R).

%% mi1( +G:goal, +G1:cont, +T1:list(cont), +AS:list(assumption), +TS:list(susreq), -R:request) is semidet.
% "defaulty" goal interpreter, built in preds in rule/3.
mi1(N:=V, G1,T1,AS,TS1,R) :- !,
   (  member(N:=V1,AS) % an assumption has alreadby been made about rv N
   -> V=V1,            % this can fail if values don't match
      mi(G1,T1,AS,TS1,R)    % carry on with remaining goals
   ;  rv(N,Dist),      % get suspension requests for each possible value of N...
      findall(susreq(N:=V,G1,P), member(P:V,Dist),TS2,TS1), % ... and stack them on TS1
      mi2(T1,AS,TS2,R) % continue with remaining active threads
   ).
mi1(G,G1,T1,AS,TS,R) :-
   % prepend list of continuations for this choice point and continue
   findall(G2,rule(G,G2,G1),T2,T1), % create new threads based on expansions of G
   mi2(T2,AS,TS,R).

%% mi2( +Alts:list(cont), +AS:list(assumption), +TS:list(susreq), -R:request) is det.
mi2([],_,Threads,sus(Threads)). % no active continuations, so return suspended continuations 
mi2([T|T1],AS,TS,R) :- mi(T,T1,AS,TS,R). % interpret first continuation

rule(X=X,GS,GS).
rule(X\=Y,GS,GS) :- X\=Y.
rule(X is Y,GS,GS) :- X is Y.
rule(or(GA,GB,G2),G1,G2) :- G1=GA; G1=GB.
rule(H,G1,G2) :- pha_user:rule(H,G1,G2).
rv(N,V) :- pha_user:rv(N,V).

%% glist(+G:goal)// is det.
%  Translates a PHA goal into a difference list representation.
glist(true) --> !, [].
glist((A,B)) --> !, glist(A), glist(B).
glist(&(A,B)) --> !, glist(A), glist(B).
glist((A;B)) --> !, [or(GA,GB,GT)], {glist(A,GA,GT), glist(B,GB,GT)}.
glist(H) --> [H].


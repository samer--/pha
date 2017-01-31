/** <module> Lazy lists with explicit metacalls.

   This module provides an alternate implementation of lazy lists
   where the tail of the list is expanded by a metacall.
   ==
   llist(A) ---> lnil ; lcons(A, pred(llist(A))).
   ==
*/

:- module(lazy, 
   [  map/3
   ,  map/4
   ,  member/2
   ,  repeat/2
   ,  to_llist/2
   ,  to_list/2
   ,  take/3
   ,  decons/3
   ,  head/2
   ,  tail/2
   ,  singleton/2
   ,  empty/1
   ]).


singleton(X, lcons(X,=(lnil))).
cons(H,TT,lcons(H,TT)).
empty(lnil).

%% head(+List:llist(A),-Head:A) is semidet.
head(lcons(X,_),X).

%% tail(+List:llist(A),-Tail:llist(A)) is semidet.
tail(lcons(_,XP),T) :- call(XP,T).

%% decons(+List:llist(A),-Head:A,-Tail:llist(A)) is semidet.
decons(lcons(X,XP),X,T) :- call(XP,T).

%% repeat(+X:A, -List:llist(A)) is det.
%  Create a list of infinitely repeating X
repeat(X, lcons(X,repeat(X))).

%% take(+N:natural, +L1:llist(A), -L2:llist(A)) is semidet.
%  L2 consists of the first N elements of L1. Traversal of L2 will
%  fail if L1 has fewer than N elements.
take(0, _, lnil).
take(N, lcons(X,XP),lcons(X,lazy:take(M,XT))) :- succ(M,N), call(XP,XT).

take1(0, _, =(lnil)).
take1(N, XP, =(lcons(X,lazy:take1(M,XT)))) :- succ(M,N), call(XP,lcons(X,XT)).

%% to_llist(+L1:llist(A),-L2:list(A)) is det.
%  Conversion from llist(A) to a Prolog list with delayed tail evaluation.
to_llist(lnil,[]).
to_llist(lcons(X,XP),[X|XX]) :- call(XP,XT), freeze(XX,to_llist(XT,XX)).

%% to_list(+L1:llist(A),-L2:list(A)) is det.
%  Conversion from llist(A) to a normal, fully evaluated Prolog list.
to_list(lnil,[]).
to_list(lcons(X,XP),[X|XX]) :- call(XP,XT), to_list(XT,XX).

%% map(+P:pred(A,B), +LA:llist(A), -LB:llist(B)) is det.
map(_,lnil,lnil).
map(P,lcons(X,XP),lcons(Y,lazy:map(P,XT))) :- 
   call(P,X,Y), call(XP,XT).  

%% map(+P:pred(A,B,C), +LA:llist(A), +LB:llist(B), -LC:llist(C)) is det.
map(_,lnil,lnil,nil).
map(P,lcons(X,XP),lcons(Y,YP),lcons(Z,lazy:map(P,XT,YT))) :- 
   call(P,X,Y,Z), call(XP,XT), call(YP,YT).  

%% member(-X:A,+List:llist(A)) is nondet.
member(X,lcons(X,_)).
member(X,lcons(_,XP)) :- call(XP,XT), member(X,XT).

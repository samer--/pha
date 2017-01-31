/** <module> Lazy lists
   
   This module provides implementations of list predicates that
   work with lists whos tails are uninstantiated until unified.
   Implemented using delayed goals (freeze/2).
*/
:- module(lazy, 
   [  map/3
   ,  map/4
   ,  repeat/2
   ,  singleton/2
   ,  head/2
   ,  tail/2
   ,  decons/3
   ,  cons/3
   ,  member/2
   ,  empty/1
   ]).

map(P,[X|XX],[Y|YY]) :- call(P,X,Y), freeze(YY,map(P,XX,YY)).
map(_,[],[]).

map(P,[X|XX],[Y|YY],[Z|ZZ]) :- call(P,X,Y,Z), freeze(ZZ,map(P,XX,YY,ZZ)).
map(_,[],[],[]).

repeat(X,[X|L]) :- freeze(L,repeat(X,L)).

unfold(P,S1,[X|XX]) :- call(P,X,S1,S2), freeze(XX,unfold(P,S2,XX)).

singleton(X,[X]).
head([X|_],X).
tail([_|X],X).
decons([H|T],H,T).
cons(H,PT,[H|T]) :- freeze(T, call(PT,T)).
empty([]).

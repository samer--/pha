:- module(priorityq,
   [  pq_insert/4
   ,  pq_remove/4
   ,  pq_size/2
   ,  pq_peek/3
   ,  pq_empty/1
   ]).

/** <module> Priority queues (thin wrapper for library(heaps)
*/

:- use_module(library(heaps)).

%% pq_empty(?Q:pq(A)) is det.
%  Unifies Q with an empty queue.
pq_empty(H) :- empty_heap(H).

%% pq_peek(-P:prio, -X:A, +Q:pq(A)) is semidet.
%  Unify X with the item at the head of the queue if non-empty.
pq_peek(P, V, H) :- min_of_heap(H,P1,V), P is -P1.

%% pq_insert(+P:prio, +X:A, +Q1:pq(A), -Q2:pq(A)) is det.
%  Insert an item into a queue.
pq_insert(P, V, H1, H2) :- P1 is -P, add_to_heap(H1, P1, V, H2).

%% pq_remove(-P:prio, -X:A, +Q1:pq(A), -Q2:pq(A)) is semidet.
%  Removes topmost value in the queue. Fails if queue empty.
pq_remove(P, V, H1, H2) :- get_from_heap(H1, P1, V, H2), P is -P1.

%% pq_size(+Q:pq(A), -N:natural) is det.
%  Unifies N with the number of items in the queue.
pq_size(H, N) :- heap_size(H, N).


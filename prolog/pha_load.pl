:- module(pha_load, [load/1, edit//0]).

:- use_module(pha_mi, [glist/3]).
:- dynamic current_program/1.

:- op(400,fx,~).
:- op(990,xfy,&).
:- op(1200,xfx,<-).

% ---------------------------------------------------------------------------
% translation and loading
% When loading a PHA program using load/1, the result is a set of clauses
% for the predicates pha_user:rv/2, pha_user:rule/3. The rule represention
% is a head term with a difference list of conjunctive subgoals. Disjunction
% is represented by the special subgoal =|or(List1,List2,Tail)|=, which is
% two difference lists sharing the same tail.

clause_translation(rv(Name,D),pha_user:rv(Name,Vals)) :- !, eval_dist(D,Vals).
clause_translation(rv(Name,D):-B, (pha_user:rv(Name,Vals):-B,eval_dist(D,Vals))) :- !.
clause_translation(H:-B, pha_user:rule(H,G1,G2)) :- !, glist(B,G1,G2).
clause_translation(H<-B, pha_user:rule(H,G1,G2)) :- !, glist(B,G1,G2).
clause_translation(H-->B, Rule) :- !, 
   dcg_translate_rule(H-->B,Cl), 
   clause_translation(Cl, Rule).
clause_translation(H, pha_user:rule(H,G1,G2)) :- glist(true,G1,G2).

eval_dist(\Dist1,Dist) :- !, maplist(flip_weighted,Dist1,Dist).
eval_dist(flip(P1),[P0:false, P1:true]) :- !, P0 is 1-P1.
eval_dist([X|XS],[X|XS]).

flip_weighted(V:P,P:V).

%% load(+FileSpec) is semidet.
%  Clears the current program and loads a new one from the given file spec.
%  The current program is not cleared if the given file cannot be read.
load(FileSpec) :-
   absolute_file_name(FileSpec, [extensions([pha,'']), access(read)], File),
   read_file_to_terms(File, Terms, [module(pha)]),
   retractall(current_program(_)),
   catch(abolish(pha_user:rule/3),_,true),
   catch(abolish(pha_user:rv/2),_,true),
   forall(member(Term,Terms), (clause_translation(Term,Clause), assertz(Clause))),
   assert(current_program(File)),
   compile_predicates([pha_user:rule/3, pha_user:rv/2]),
   (predicate_property(pha_user:rule(_,_,_),number_of_clauses(NC)) -> true; NC=0),
   (predicate_property(pha_user:rv(_,_),number_of_clauses(NR)) -> true; NR=0),
   format('% pha> ~w compiled: ~d random variables, ~d clauses.\n',[File,NR,NC]).

%% edit// is det.
%  Edit loaded program.
edit --> {current_program(File), edit(File), load(File)}.

clause_expansion(H:-B,pha_user:rule(H,GS,GT)) :- glist(B,GS,GT).

check_rv(Name,Vals) :-
   (  \+ (numbervars(Name,0,_), \+ground(Vals)) -> true
   ;  format('WARNING: rv ~w has non-ground values - ignoring it.\n',[Name])
   ).

user:term_expansion(\H, EXP) :- findall(X, clause_expansion(H:-true, X), EXP).
user:term_expansion(\H:-B, EXP) :- findall(X, clause_expansion(H:-B, X), EXP).
user:term_expansion(rv(Name,Vals),pha_user:rv(Name,Vals)) :- check_rv(Name,Vals).

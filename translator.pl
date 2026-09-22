/*  ==========================================================================
    translator.pl

    Prototype translator for a proximity-based probabilistic logic programming
    language.

    Supported source programs satisfy the following restrictions:

      * P is finite, definite, and function-free;
      * probabilistic facts are ground;
      * proximity declarations are between distinct constants;
      * all probabilities are in [0,1];
      * queries handled by the front end are ground.

    Translation tau:

      If the source contains no proximity declarations, it is already a
      standard ProbLog program and is emitted unchanged (up to formatting).

      Otherwise:

      p :: q(c1,...,cn).      ->  p :: q_aux(c1,...,cn).
      s1 ~ s2 = p.            ->  p :: prox(s1,s2).

      equals(X,X).
      equals(X,Y) :- prox(X,Y).
      equals(X,Y) :- prox(Y,X).

      p(t1,...,tn) :- B.      ->  p_aux(t1,...,tn) :- B.

      p(X1,...,Xn) :- p_aux(Y1,...,Yn),
                       equals(X1,Y1),...,equals(Xn,Yn).

    Body atoms keep their original predicate names, so calls in clause bodies
    also pass through wrappers. Ground queries are unchanged.
    ==========================================================================
*/

:- module(proximity_problog,
          [ translate_file/2,
            translate_file/3,
            translate_terms/2,
            read_source/2,
            validate_items/1
          ]).

:- use_module(library(apply)).
:- use_module(library(lists)).

% Operators used by the source language and by the internal representation.
:- op(200, xfy, ::).
:- op(500, xfx, ~).
:- op(200, xfy, user:(::)).
:- op(500, xfx, user:(~)).

% ============================================================================
% 1. READING
% ============================================================================

read_source(File, Items) :-
    setup_call_cleanup(
        open(File, read, Stream),
        read_all_terms(Stream, Items),
        close(Stream)).

read_all_terms(Stream, Items) :-
    read_term(Stream, Term, [module(proximity_problog)]),
    ( Term == end_of_file
    -> Items = []
    ;  classify_term(Term, Item),
       Items = [Item|Rest],
       read_all_terms(Stream, Rest)
    ).

classify_term(Prob :: Fact, pfact(Fact, Prob)) :- !.
classify_term((S1 ~ S2) = Prob, prox(S1, S2, Prob)) :- !.
classify_term(query(Atom), query(Atom)) :- !.
classify_term((Head :- Body), clause(Head, Body)) :- !.
classify_term(Head, clause(Head, true)).

% ============================================================================
% 2. VALIDATION
% ============================================================================

validate_items(Items) :-
    maplist(validate_item, Items),
    validate_unique_probabilistic_facts(Items),
    validate_unique_proximities(Items),
    validate_fresh_generated_predicates(Items),
    validate_queries_defined(Items).

% Ensure that every queried predicate is defined in the source program.
validate_queries_defined(Items) :-
    findall(Name/Arity,
            ( member(pfact(F,_), Items), functor(F,Name,Arity) ),
            FromPFacts),
    findall(Name/Arity,
            ( member(clause(H,_), Items), functor(H,Name,Arity) ),
            FromClauses),
    append(FromPFacts, FromClauses, Defined),
    forall(member(query(A), Items),
           ( functor(A, Name, Arity),
             ( memberchk(Name/Arity, Defined)
             -> true
             ;  source_error('query refers to a predicate with no definition anywhere in the program (no matching clause head or probabilistic fact)', Name/Arity)
             )
           )).

validate_item(pfact(Fact, Prob)) :- !,
    validate_probability(Prob),
    validate_atom(Fact, probabilistic_fact),
    ( ground(Fact)
    -> true
    ;  source_error('probabilistic facts must be ground', Fact)
    ).
validate_item(prox(S1, S2, Prob)) :- !,
    validate_probability(Prob),
    validate_constant(S1, proximity_left),
    validate_constant(S2, proximity_right),
    ( S1 \== S2
    -> true
    ;  source_error('proximity declarations must be non-reflexive; reflexivity is implicit', S1 ~ S2)
    ).
validate_item(clause(Head, Body)) :- !,
    validate_atom(Head, clause_head),
    validate_body(Body).
validate_item(query(Atom)) :- !,
    validate_atom(Atom, query),
    ( ground(Atom)
    -> true
    ;  source_error('queries must be ground', Atom)
    ).
validate_item(Item) :-
    source_error('unsupported source item', Item).

validate_probability(P) :-
    ( number(P), P >= 0, P =< 1
    -> true
    ;  source_error('probability must be a number in [0,1]', P)
    ).

validate_constant(C, _Where) :-
    ( nonvar(C), atomic(C)
    -> true
    ;  source_error('proximity declarations must relate constants (no variables or compound terms)', C)
    ).

validate_atom(Atom, _Where) :-
    ( callable(Atom), nonvar(Atom), Atom \= (_,_), Atom \= (_;_), Atom \= (_->_)
    -> Atom =.. [Name|Args],
       ( atom(Name)
       -> maplist(validate_term, Args)
       ;  source_error('predicate symbol must be an atom', Atom)
       )
    ;  source_error('expected an atom', Atom)
    ).

validate_term(Term) :-
    ( var(Term)
    -> true
    ;  atomic(Term)
    -> true
    ;  source_error('the source language is function-free; compound terms are not allowed', Term)
    ).

validate_body(true) :- !.
validate_body((A,B)) :- !,
    validate_body(A),
    validate_body(B).
validate_body(Atom) :-
    validate_atom(Atom, clause_body).

validate_unique_probabilistic_facts(Items) :-
    findall(F, member(pfact(F,_), Items), Facts),
    sort(Facts, Unique),
    length(Facts, N), length(Unique, U),
    ( N =:= U
    -> true
    ;  source_error('the same probabilistic fact occurs more than once', Facts)
    ).

validate_unique_proximities(Items) :-
    findall(Key,
            ( member(prox(A,B,_), Items), unordered_pair(A,B,Key) ),
            Keys),
    sort(Keys, Unique),
    length(Keys, N), length(Unique, U),
    ( N =:= U
    -> true
    ;  source_error('a proximity pair occurs more than once (symmetry means a~b and b~a are the same declaration)', Keys)
    ).

unordered_pair(A, B, pair(A,B)) :- A @=< B, !.
unordered_pair(A, B, pair(B,A)).

% The translation assumes prox/2, equals/2 and all *_aux predicates are fresh.
validate_fresh_generated_predicates(Items) :-
    source_predicate_symbols(Items, Symbols),
    forall(member(Name/Arity, Symbols),
           validate_source_predicate_name(Name, Arity)).

validate_source_predicate_name(prox, 2) :- !,
    source_error('prox/2 is reserved by the translation', prox/2).
validate_source_predicate_name(equals, 2) :- !,
    source_error('equals/2 is reserved by the translation', equals/2).
% Reject predicate names reserved by ProbLog.
validate_source_predicate_name(Name, Arity) :-
    memberchk(Name, [query, evidence]), !,
    source_error('this predicate name is reserved by ProbLog', Name/Arity).
validate_source_predicate_name(Name, Arity) :-
    ( atom_concat(_, '_aux', Name)
    -> source_error('predicate names ending in _aux are reserved by the translation', Name/Arity)
    ;  true
    ).

source_predicate_symbols(Items, Symbols) :-
    findall(S,
            ( member(Item, Items), item_predicate_symbol(Item, S) ),
            All),
    sort(All, Symbols).

item_predicate_symbol(pfact(F,_), Name/Arity) :- functor(F, Name, Arity).
item_predicate_symbol(clause(H,B), S) :-
    ( functor(H, Name, Arity), S = Name/Arity
    ; body_predicate_symbol(B, S)
    ).
item_predicate_symbol(query(A), Name/Arity) :- functor(A, Name, Arity).

body_predicate_symbol(true, _) :- !, fail.
body_predicate_symbol((A,B), S) :- !,
    ( body_predicate_symbol(A,S) ; body_predicate_symbol(B,S) ).
body_predicate_symbol(A, Name/Arity) :- functor(A, Name, Arity).

source_error(Message, Culprit) :-
    throw(error(domain_error(proximity_problog_source, Culprit),
                context(proximity_problog, Message))).

% ============================================================================
% 3. TRANSLATION
% ============================================================================

translate_terms(Items, ProblogTerms) :-
    validate_items(Items),
    partition_items(Items, PFacts, Proxs, Clauses, Queries),
    ( Proxs == []
    -> % Programs without proximity declarations are emitted unchanged.
       maplist(source_item_to_problog_term, Items, ProblogTerms)
    ;  maplist(pfact_to_aux_term, PFacts, PFactTerms),
       maplist(prox_to_fact_term, Proxs, ProxTerms),
       equals_relation_terms(ProxTerms, EqualsTerms),
       maplist(clause_to_aux_term, Clauses, AuxClauseTerms),
       predicate_symbols(Clauses, PFacts, PredSymbols),
       maplist(wrapper_term, PredSymbols, WrapperTerms),
       maplist(query_to_term, Queries, QueryTerms),

       append([PFactTerms, ProxTerms, EqualsTerms,
               AuxClauseTerms, WrapperTerms, QueryTerms],
              ProblogTerms)
    ).

% Reconstruct source terms without introducing auxiliaries.
source_item_to_problog_term(pfact(Fact, Prob), (Prob :: Fact)).
source_item_to_problog_term(clause(Head, true), Head) :- !.
source_item_to_problog_term(clause(Head, Body), (Head :- Body)).
source_item_to_problog_term(query(A), query(A)).

partition_items(Items, PFacts, Proxs, Clauses, Queries) :-
    include(is_pfact, Items, PFacts),
    include(is_prox, Items, Proxs),
    include(is_clause, Items, Clauses),
    include(is_query, Items, Queries).

is_pfact(pfact(_,_)).
is_prox(prox(_,_,_)).
is_clause(clause(_,_)).
is_query(query(_)).

pfact_to_aux_term(pfact(Fact, Prob), (Prob :: AuxFact)) :-
    aux_atom(Fact, AuxFact).

prox_to_fact_term(prox(S1, S2, Prob), (Prob :: prox(S1,S2))).

% This predicate is used only when at least one proximity declaration exists;
% the no-proximity case is handled earlier by emitting the source program
% unchanged.
equals_relation_terms(_ProxTerms, [
    equals_fact_marker(equals(X,X)),
    (equals(X,Y) :- prox(X,Y)),
    (equals(X,Y) :- prox(Y,X))
]).

clause_to_aux_term(clause(Head, true), AuxHead) :- !,
    aux_atom(Head, AuxHead).
clause_to_aux_term(clause(Head, Body), (AuxHead :- Body)) :-
    aux_atom(Head, AuxHead).

aux_atom(Atom, AuxAtom) :-
    Atom =.. [Name|Args],
    atom_concat(Name, '_aux', AuxName),
    AuxAtom =.. [AuxName|Args].

predicate_symbols(Clauses, PFacts, Symbols) :-
    findall(Name/Arity,
            ( member(clause(Head,_), Clauses), functor(Head,Name,Arity) ),
            FromClauses),
    findall(Name/Arity,
            ( member(pfact(Fact,_), PFacts), functor(Fact,Name,Arity) ),
            FromPFacts),
    append(FromClauses, FromPFacts, All),
    sort(All, Symbols).

% Nullary predicates follow the same uniform translation. Since there are no
% arguments to compare, the wrapper contains no equals/2 calls.
wrapper_term(Name/0, (Head :- AuxHead)) :- !,
    Head =.. [Name],
    atom_concat(Name, '_aux', AuxName),
    AuxHead =.. [AuxName].
wrapper_term(Name/Arity, (Head :- Body)) :-
    length(Xs, Arity),
    length(Ys, Arity),
    Head =.. [Name|Xs],
    atom_concat(Name, '_aux', AuxName),
    AuxHead =.. [AuxName|Ys],
    pairwise_equals(Xs, Ys, EqGoals),
    conjoin([AuxHead|EqGoals], Body).

pairwise_equals([], [], []).
pairwise_equals([X|Xs], [Y|Ys], [equals(X,Y)|Rest]) :-
    pairwise_equals(Xs, Ys, Rest).

conjoin([G], G) :- !.
conjoin([G|Gs], (G,Rest)) :- conjoin(Gs, Rest).

query_to_term(query(A), query(A)).

% ============================================================================
% 4. FILE-TO-FILE COMPILATION AND OUTPUT
% ============================================================================

translate_file(InFile, OutFile) :-
    translate_file(InFile, OutFile, []).

translate_file(InFile, OutFile, _Options) :-
    read_source(InFile, Items),
    translate_terms(Items, Terms),
    ensure_output_directory(OutFile),
    setup_call_cleanup(
        open(OutFile, write, Out),
        write_problog_program(Out, InFile, Terms),
        close(Out)),
    length(Terms, N),
    format(user_error, '~N% Translated ~w -> ~w (~d generated terms).~n',
           [InFile, OutFile, N]).

ensure_output_directory(OutFile) :-
    file_directory_name(OutFile, Dir),
    ( Dir == '.' ; Dir == '' ; exists_directory(Dir) ), !.
ensure_output_directory(OutFile) :-
    file_directory_name(OutFile, Dir),
    make_directory_path(Dir).

write_problog_program(Out, InFile, Terms) :-
    format(Out, '% Generated by the proximity-to-ProbLog translator.~n', []),
    format(Out, '% Source: ~w~n~n', [InFile]),
    forall(member(T0, Terms),
           ( copy_term(T0,T),
             numbervars(T,0,_),
             write_problog_term(Out,T)
           )).

write_problog_term(Out, (Prob :: Fact)) :- !,
    writeterm(Out, Prob), format(Out, '::', []), writeterm(Out, Fact),
    format(Out, '.~n', []).
write_problog_term(Out, equals_fact_marker(Fact)) :- !,
    writeterm(Out, Fact), format(Out, '.~n', []).
write_problog_term(Out, (Head :- Body)) :- !,
    writeterm(Out, Head), format(Out, ' :-~n    ', []),
    write_body(Out, Body), format(Out, '.~n', []).
write_problog_term(Out, query(A)) :- !,
    nl(Out), format(Out, 'query(', []), writeterm(Out, A), format(Out, ').~n', []).
write_problog_term(Out, Fact) :-
    writeterm(Out, Fact), format(Out, '.~n', []).

write_body(Out, (G,Rest)) :- !,
    writeterm(Out,G), format(Out, ',~n    ', []), write_body(Out,Rest).
write_body(Out, G) :- writeterm(Out,G).

writeterm(Out, T) :-
    write_term(Out, T, [quoted(true), numbervars(true)]).

%% -*- prolog -*-
/*
    Copyright Éric Würbel, LSIS-CNRS UMR7196, (2012-2015)

    <eric.wurbel@lsis.org>

    This software is a computer program whose purpose is to perform
    removed-set fusion of knowledge bases represented by logic programs.

    This software is governed by the CeCILL license under French law and
    abiding by the rules of distribution of free software.  You can use,
    modify and/ or redistribute the software under the terms of the
    CeCILL license as circulated by CEA, CNRS and INRIA at the following
    URL "http://www.cecill.info".

    As a counterpart to the access to the source code and rights to
    copy, modify and redistribute granted by the license, users are
    provided only with a limited warranty and the software's author, the
    holder of the economic rights, and the successive licensors have
    only limited liability.

    In this respect, the user's attention is drawn to the risks
    associated with loading, using, modifying and/or developing or
    reproducing the software by the user in light of its specific status
    of free software, that may mean that it is complicated to
    manipulate, and that also therefore means that it is reserved for
    developers and experienced professionals having in-depth computer
    knowledge. Users are therefore encouraged to load and test the
    software's suitability as regards their requirements in conditions
    enabling the security of their systems and/or data to be ensured
    and, more generally, to use and operate it in the same conditions as
    regards security.

    The fact that you are presently reading this means that you have had
    knowledge of the CeCILL license and that you accept its terms.

    This module implements the ASP encoding of the different
    merging strategies.
*/



:- module(strategy, [
		     gen_strategy/3,
		     pre/2,
		     equiv_rule_true/3
		    ]).

:- use_module(logic).
:- use_module(utils, [
		      integer_enum/3,
		      integer_enuml/3
		     ]).
:- use_module(asp).
:- use_module(generator, [
			  collect_rule_atoms/2,
			  kbnames/1,
			  get_rules/3
			 ]).
:- use_module(swiprolog, [concatenate/3]).

:- use_module(library(clpfd)).



%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	pre computation for card strategy : remove duplicate rules


%%	pre(+Profile, -NewProfile)
%%
%%	NewProfile is Profile without duplicates if current strategy is
%%	is card.

pre(Profile,Profile) :-
	nb_getval(strategy,S),
	S \== card,
	!
	.
pre(Profile,NProfile) :-
	nb_getval(strategy,card),
	remove_duplicates(Profile,NProfile)
	.

%%	remove_duplicates(+Profile,-NewProfile)
%%
%%	NewProfile is Profile without duplicates.

remove_duplicates([],[]).
remove_duplicates([Name-Wff|KBs], [Name-Wff|FilteredKBs]) :-
	rdup(KBs,Wff,NKBs),
	remove_duplicates(NKBs,FilteredKBs)
	.

%%	rdup(+Profile,+RuleConj,-NewProfile)
rdup(KBs, (A,B), NKBs) :-
	rdup(KBs,A,KBs1),
	rdup(KBs1,B,NKBs),
	!
	.
rdup(KBs, (H :- B), NKBs) :-
	rdup2(KBs,(H :- B),NKBs),
	!
	.
rdup(KBs, (:- B), NKBs) :-
	rdup2(KBs,(:- B),NKBs)
	.
rdup(KBs, H, NKBs) :-
	callable(H),
	rdup2(KBs,H,NKBs)
	.

rdup2([],_,[]).
rdup2([Name-KB|KBs],Rule,[Name-NewKB|NewKBs]) :-
	apply_to_conjuncts(KB,strategy:equiv_rule_true,Rule,NewKB),
	rdup2(KBs,Rule,NewKBs)
	.

%%	equiv_rule_true(?R1,?R2,?R3)
%%
%%	R3 unifies with true if R1 and R2 are equivalent rules, i.e.
%	they have the same and their bodies contain the same terms.
%	R3 unifies with R1 if R1 and R2 are not equivalent.

equiv_rule_true(R,R,true).
equiv_rule_true((H :- B1), (H :- B2), true) :-
	inc_body(B1,B2),
	inc_body(B2,B1)
	.
equiv_rule_true((:- B1), (:- B2), true) :-
	inc_body(B1,B2),
	inc_body(B2,B1)
	.
equiv_rule_true((H1 :- B1), (H2 :- _), (H1 :- B1)) :-
	H1 \= H2
	.
equiv_rule_true((H1 :- B1), (_ :- B2), (H1 :- B1)) :-
	(   \+ inc_body(B1,B2) ; \+ inc_body(B2,B1) )
	.
equiv_rule_true((:- B1), (:- B2), (:- B1)) :-
	(   \+ inc_body(B1,B2) ; \+ inc_body(B2,B1) )
	.
equiv_rule_true(T1,T2,T1) :-
	callable(T1),
	T1 \= T2
	.

%%	inc_body(Body1,Body2)
%%
%%      True if Body1 is included in Body2.

inc_body((A,B), Body2) :-
	inc_body(A,Body2),
	inc_body(B,Body2)
	.
inc_body(A, Body2) :-
	A \= (_,_),
	in_body(A,Body2)
	.

in_body(A, (A,_)).
in_body(A, A) :-
	A \= (_,_)
	.
in_body(A, (B,C)) :-
	A \= B,
	in_body(A,C)
	.

%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	Strategy_generation

%%	gen_strategy(+Strat, +Profile, -Rules)
%%	Upon success, Rules is unified with a conjunction of ASP rules
%%	which implement the merging strategy Strat for profile Profile.

% all potential removed sets

gen_strategy(all, _, Rules) :-
	% #### maybe useless in our case. (-> to check)
	rule_atoms_exclusion(Rules)
	.
% inclusion-minimal potential removed sets
% no generation is performed here. The gathering of the
% inclusion-minimal potential removed sets is performed by
% post-filtering the collection of potential removed sets.
%
% This is really inefficient !

gen_strategy(inclmin, _, true).

% sigma strategy

gen_strategy(sigma, Profile, '#minimize' WL) :-
	collect_rule_atoms(Profile,RAtoms),
	simple_weight_list(RAtoms,WL)
	.
% card strategy. (same as sigma, the removal of duplicates
% has been performed earlier).

gen_strategy(card, Profile, '#minimize' WL) :-
	collect_rule_atoms(Profile,RAtoms),
	simple_weight_list(RAtoms,WL)
	.
% max strategy.
% Be careful ! The rules generated here are not sufficient by themselve,
% the results have to be post-filtered in order to keep only removed
% sets which are minimal w.r.t. set inclusion regarding rsf/2 atoms.

gen_strategy(max, Profile, Repr) :-
	max_rules(Profile, M),
	domain(possible, 'U', DomPoss),
	fact_intrv(possible, 0, M, Possible),
	size_preds('U', possible, Size),
	max_size('U', possible, MaxSize),
	integer_enuml(1, M, AL),
	integer_enum(1, M, L),
	minimize(max/1, AL, L, Min),
	n_conjoin([DomPoss, Possible, Size, MaxSize, Min], Repr)
	.
% gmax strategy
% Be careful ! The rules generated here are not sufficient by themselve,
% the results have to be post-filtered in order to keep only removed
% sets which are minimal w.r.t. set inclusion regarding rsf/2 atoms.

gen_strategy(gmax, Profile, Repr) :-
	length(Profile, N),
	max_rules(Profile, M),
	domain(possible, 'U', DomPoss),
	domain(base, 'V', DomBase),
	fact_intrv(possible, 0, M, Possible),
	fact_intrv(base, 1, N, Base),
	size_base_preds('U', possible, Size),
	max_size_lex(N, Max),
	gmax_minimize_list(M, N, MinList),
	n_conjoin([DomPoss, DomBase, Possible, Base, Size, Max,
		   '#minimize' MinList], Repr)
	.

%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	Generation auxiliary predicates


%%	simple_weight_list(?Atoms, ?WeightedAtoms)
%%
%%	WeightedAtoms is a list of weighted atoms for
%	clingo/gringo #minimize statements. Weights are all considered
%	to be equal to 1. For clingo versions <=3, the two lists are the
%	same. For clingo versions >=4, each atom a generates a weighted
%	atom 1@a:a.

simple_weight_list(Atoms, Atoms) :-
	nb_getval(claspver, 3)
	.
simple_weight_list(Atoms, WL) :-
	nb_getval(claspver, V), V #>= 4,
	swl(Atoms, WL)
	.

swl([], []).
swl([A|AL], [(1,A:A)|WL]) :-
	swl(AL, WL)
	.

%%	rule_atoms_exclusion(?Rules)
%%
%%	True if Rules represents the rule atoms exclusion rules for the
%	current belief profile. These rules are only needed to compute
%	all the potential removed sets.

rule_atoms_exclusion(Rules) :-
	bagof(A,Name^R^get_rules(Name,R,A),RAtoms), % collect rule atoms
	rule_atoms_excl(RAtoms,Rules)
	.

rule_atoms_excl([],true).
rule_atoms_excl([A|L],Rules) :-
	var(A),
	rule_atoms_excl(L,Rules)
	.
rule_atoms_excl([A|L],Rules) :-
	\+ var(A),
	rule_atoms_excl(L,Rules1),
	conjoin(1 // [A, -A] // 1,Rules1,Rules)
	.

%%	gmax_minimize_list(+MaxNbForm,+NbBases,-List)
%%	Upon success, List is unified with the minimize literal
%%	list for the gmax strategy, based on the number of bases and
%%	the maximal number of formulae in a knowledge base.
%%	If S_i represent the number of formula atoms in base K_i for a
%	given removed set, and (S_1,...,S_n) is the sequence of S_i
%	sorted in descending order, then, in order to compare such
%	sequences, the following polynom is computed :
%	S_n + S_(n-1) * (m+1)^1 + ... + S_1 * (m+1)^(n-1)

gmax_minimize_list(M,N,L) :-
	nb_getval(claspver, 3),
	gmax_minimize_list(M,N,N,L)
	.
gmax_minimize_list(M,N,L) :-
	nb_getval(claspver, V), V #>= 4,
	gmax_minimize_list2(M,N,N,L)
	.

gmax_minimize_list(_,_,0,[]).
gmax_minimize_list(M,N,I,L) :-
	gmax_n(M,M,N,I,L1),
	I1 #= I-1,
	append(L1,L2,L),
	gmax_minimize_list(M,N,I1,L2)
	.

gmax_n(_,0,_,I,[Term=V]) :-
	!,
	concatenate(max,I,Functor),
	Term =.. [Functor,0],
	V #= 0
	.
gmax_n(M,J,N,I,[Term=V|L]) :-
	concatenate(max,I,Functor),
	Term =.. [Functor,J],
	V #= J * (M + 1) ^ (N - I),
	J1 #= J - 1,
	gmax_n(M,J1,N,I,L)
	.

gmax_minimize_list2(_,_,0,[]).
gmax_minimize_list2(M,N,I,L) :-
	gmax_n2(M,M,N,I,L1),
	I1 #= I-1,
	append(L1,L2,L),
	gmax_minimize_list2(M,N,I1,L2)
	.

%%	Version for gringo 4 and up. The minimize syntax has changed.
%%	old : #minimize [ l=w, ... ]. new : #minimize { w : l; ... }.
%%	(what is nice with standards is that there are so many to choose
%	from...)

gmax_n2(_,0,_,I,[(V,Term:Term)]) :-
	!,
	concatenate(max,I,Functor),
	Term =.. [Functor,0],
	V #= 0
	.
gmax_n2(M,J,N,I,[(V,Term:Term)|L]) :-
	concatenate(max,I,Functor),
	Term =.. [Functor,J],
	V #= J * (M + 1) ^ (N - I),
	J1 #= J - 1,
	gmax_n2(M,J1,N,I,L)
	.


%%	minimize(?Pred, ?ArgsList, ?WeightList, ?Repr)
%%
%%	Repr unifies with a #minimize statement on Pred (which is in
%%      the form predicate_name/arity) with arguments in ArgList
%%      and weights in wheightlist

minimize(PredSpec,ArgsL,WL,'#minimize' L) :-
	nb_getval(claspver, 3),
	length(ArgsL,Len),
	length(WL,Len),
	weight_list(PredSpec,ArgsL,WL,L)
	.
minimize(PredSpec,ArgsL,WL,'#minimize' L) :-
	nb_getval(claspver, V), V #>= 4,
	length(ArgsL,Len),
	length(WL,Len),
	weight_list2(PredSpec,ArgsL,WL,L)
	.

weight_list(_,[],[],[]).
weight_list(Pred/Arity,[A|AL],[W|WL],[Inst=W|SL]) :-
	length(A,Arity),
	Inst =.. [Pred|A],
	weight_list(Pred/Arity,AL,WL,SL)
	.

%%	Version for gringo 4 and up. The minimize syntax has changed.
%%	old : #minimize [ l=w, ... ]. new : #minimize { w : l; ... }.
%%	(what is nice with standards is that there are so many to choose
%	from...)

weight_list2(_,[],[],[]).
weight_list2(Pred/Arity,[A|AL],[W|WL],[(W,Inst:Inst)|SL]) :-
	length(A,Arity),
	Inst =.. [Pred|A],
	weight_list2(Pred/Arity,AL,WL,SL)
	.

%%	domain(PredName, VarName, DomainDirective)
%%
%%	true if DomainDirective is a clasp #domain directive over
%%	predicate PredName for variable VarName. grigo/clingo version
%	4.x prohibits such constructs, thus in this case DomainDirective
%	unifies with true.

domain(PN, Arg, '#domain' Func) :-
	nb_getval(claspver, 3),
	Func =.. [PN,'$VAR'(Arg)]
	.
domain(_,_,true) :-
	nb_getval(claspver, V),
	V #>= 4
	.

%%	fact_intrv(PredName,Min,Max,Fact)
%%
%%	Generate a fact with one argument ranging in the interval
%%	Min..Max.

fact_intrv(Pred,Min,Max,F) :-
	F =.. [Pred,Min .. Max]
	.

%%	size_preds(?VarName, ?DomPred, ?Repr)
%%
%%	Repr unifies the rule representing a size/1 predicate over
%%	variable VarName. This is used by the Max strategy.

size_preds(VarName, _, Repr) :-
	nb_getval(claspver, 3),
	kbnames(KBNames),
	size_pred(VarName,KBNames,Repr)
	.
size_preds(VarName, DomPred, Repr) :-
	nb_getval(claspver, V), V #>= 4,
	kbnames(KBNames),
	size_pred(VarName, DomPred, KBNames,Repr)
	.

size_pred(_, [], true).
size_pred(VarName, [Name|Names], Rules) :-
	bagof(A, R^get_rules(Name,R,A), RAtoms),
	size_pred(VarName, Names, Rs),
	conjoin((size('$VAR'(VarName)) :- '$VAR'(VarName) // RAtoms // '$VAR'(VarName)), Rs, Rules)
	.

size_pred(_, _, [], true).
size_pred(VarName, DomPred, [Name|Names], Rules) :-
	bagof(A, R^get_rules(Name,R,A), RAtoms),
	DomCall =.. [DomPred, '$VAR'(VarName)],
	size_pred(VarName, DomPred, Names, Rs),
	conjoin((size('$VAR'(VarName)) :- DomCall, '$VAR'(VarName) // RAtoms // '$VAR'(VarName)), Rs, Rules)
	.


%%	max_size(?VarName, ?DomPred, ?Rules)
%%
%%	Rules unifies with the conjunction of rules defining the max/
%%	predicate over variable VarName. This is used by the Max
%	Strategy.

max_size(U, _, Clauses) :-
	nb_getval(claspver, 3),
	domain(possible,'W',DomW),
	n_conjoin([DomW,
		   (negmax('$VAR'('W')) :- size('$VAR'(U)), '$VAR'(U) > '$VAR'('W')),
		   (max('$VAR'(U)) :- size('$VAR'(U)), not negmax('$VAR'(U)))], Clauses)
	.
max_size(U, DomPred, Clauses) :-
	nb_getval(claspver, V), V #>= 4,
	DomCallU =.. [DomPred, '$VAR'(U)],
	DomCallW =.. [DomPred, '$VAR'('W')],
	n_conjoin([
	    (negmax('$VAR'('W')) :-
	        DomCallU, DomCallW, size('$VAR'(U)), '$VAR'(U) > '$VAR'('W')),
	    (max('$VAR'(U)) :-
	        DomCallU, size('$VAR'(U)), not negmax('$VAR'(U)))
	], Clauses)
	.

%%	size_base_preds(?VN1, ?DomPred, ?Repr)
%%
%%	Repr unifies with the conjunction of rules size/2 defined over
%	variables VN1 and an index in range 1..number of bases in the
%	profile. This is used by the gmax strategy. VN1 variable ranges
%	in domain predicate DomPred.

size_base_preds(VarName1, _, Repr) :-
	nb_getval(claspver, 3),
	kbnames(KBNames),
	size_base_pred(VarName1, KBNames, Repr, 1)
	.
size_base_preds(VarName1, DomPred, Repr) :-
	nb_getval(claspver, V), V #>= 4,
	kbnames(KBNames),
	size_base_pred(VarName1, DomPred, KBNames, Repr, 1)
	.

%%	for gringo version 3 and less : VarName1 is constrained by
%	#domain

size_base_pred(_, [], true, _).
size_base_pred(VarName1,[Name|Names], Rules,I) :-
	bagof(A,R^get_rules(Name,R,A),RAtoms), % collect rule atoms
	I1 #= I+1,
	size_base_pred(VarName1,Names,Rs,I1),
	conjoin((size('$VAR'(VarName1),I) :- '$VAR'(VarName1) // RAtoms // '$VAR'(VarName1)),Rs,Rules)
	.

%%	For gringo version 4 and up : no more #domain

size_base_pred(_, _, [], true, _).
size_base_pred(VarName1, DomPred, [Name|Names], Rules, I) :-
	bagof(A,R^get_rules(Name,R,A),RAtoms), % collect rule atoms
	I1 #= I+1,
	DomCall =.. [DomPred, '$VAR'(VarName1)],
	size_base_pred(VarName1, DomPred, Names, Rs, I1),
	conjoin((size('$VAR'(VarName1),I) :- DomCall, '$VAR'(VarName1) // RAtoms // '$VAR'(VarName1)),Rs,Rules)
	.


var_n(VName,Bound,Bound,['$VAR'(V)]) :-
	!,
	concatenate(VName,Bound,V)
	.
var_n(VName,N,Bound,['$VAR'(V)|L]) :-
	N #< Bound,
	concatenate(VName,N,V),
	N1 #= N + 1,
	var_n(VName,N1,Bound,L)
	.

%%	funct_n(+Functor,+VarName,+Bound,-Term)
%%
%%	Term is unified with a Functor/Bound term, each argument being a
%%	'$VAR'(Xn) Xn being a variable name build out of VarName
%%	concatenated with a index ranging from 1 to Bound.
%%	e.g. :
%%	funct_n(f,'V',3,T)
%%	T = f(V1, V2, V3)

funct_n(FctName,Var,N,Term) :-
	var_n(Var,1,N,List),
	Term =.. [FctName|List]
	.

%%	size2_n(+Inf,+Sup,+VName1,+VName2,-Term)
%%
%%	Term is a conjunction of size/2 terms buils as for the following
%%	example :
%%	size2_n(1, 4, 'X', 'Y', T)
%%	T = (size(X1,Y1), size(X2,Y2), size(X3,Y3), size(X4,Y4))

size2_n(Bound,Bound,V1,V2,size('$VAR'(VN1),'$VAR'(VN2))) :-
	!,
	concatenate(V1,Bound,VN1),
	concatenate(V2,Bound,VN2)
	.
size2_n(N,Bound,V1,V2,Conj) :-
	N < Bound,
	concatenate(V1,N,VN1),
	concatenate(V2,N,VN2),
	N1 #= N+1,
	conjoin(size('$VAR'(VN1),'$VAR'(VN2)),Conj1,Conj),
	size2_n(N1,Bound,V1,V2,Conj1)
	.

%%	chain_op(+operator,+Min,+Max,+VarName,-Term)
%%
%%	Term unifies with a conjunction of op/2 terms which are
%%	"chaining" indexed variables.
%%	example:
%%	chain_op(==,1,3,'X',T)
%%	T = (X1==X2, X2==X3)

chain_op(Op,N1,N,V,Term) :-
	N1 #= N - 1,
	Term =.. [Op,'$VAR'(V1),'$VAR'(V2)],
	concatenate(V,N1,V1),
	concatenate(V,N,V2)
	.
chain_op(Op,N1,N,V,Conj) :-
	N1 #< N - 1,
	N2 #= N1 + 1,
	concatenate(V,N1,V1),
	concatenate(V,N2,V2),
	Term =.. [Op,'$VAR'(V1),'$VAR'(V2)],
	conjoin(Term,Conj1,Conj),
	chain_op(Op,N2,N,V,Conj1)
	.

%%	all_op(+operator,+Min,+Max,+VarName,-Term)
%%
%%	Term unifies with a conjunction of op/2 terms which are
%%	applied to all possible combinings of indexed variables, except
%%	reflexivity cases.
%%	example:
%%	chain_op(==,1,3,'X',T)
%%	T = (X1==X2, X1==X3, X2==X3)

all_op(Op,I,N,V,Term) :-
	I #= N - 1,
	J #= I + 1,
	all_op2(Op,I,J,N,V,Term)
	.
all_op(Op,I,N,V,Term) :-
	I #< N - 1,
	I2 #= I + 1,
	all_op2(Op,I,I2,N,V,Term1),
	all_op(Op,I2,N,V,Term2),
	conjoin(Term1,Term2,Term3),
	flatten_conjunction(Term3,Term)
	.

% I = J = N
all_op2(_,N,N,N,_,true) :-
	!.
% I = J, J < N
all_op2(Op,J,J,N,V,Term) :-
	J #< N,
	!,
	J2 #= J + 1,
	all_op2(Op,J,J2,N,V,Term)
	.
% I != J, J = N
all_op2(Op,I,N,N,V,Term) :-
	I #\= N,
	!,
	concatenate(V,I,V1),
	concatenate(V,N,V2),
	Term =.. [Op,'$VAR'(V1),'$VAR'(V2)]
	.
% I != J, J < N
all_op2(Op,I,J,N,V,Term) :-
	I #\= J,
	J #< N,
	!,
	J2 #= J + 1,
	concatenate(V,I,V1),
	concatenate(V,J,V2),
	Term1 =.. [Op,'$VAR'(V1),'$VAR'(V2)],
	conjoin(Term1,Term2,Term),
	all_op2(Op,I,J2,N,V,Term2)
	.



%%	chain_ge(+Min,+Max,+VarName,-Term)
%%
%%	This a a specialized version of the chain_op predicate for the
%%	functor >=/2.

chain_ge(N1,N,V,'$VAR'(V1) >= '$VAR'(V2)) :-
	N1 #= N - 1,
	concatenate(V,N1,V1),
	concatenate(V,N,V2)
	.
chain_ge(N1,N,V,Conj) :-
	N1 #< N - 1,
	N2 #= N1 + 1,
	concatenate(V,N1,V1),
	concatenate(V,N2,V2),
	conjoin('$VAR'(V1) >= '$VAR'(V2),Conj1,Conj),
	chain_ge(N2,N,V,Conj1)
	.

%%	max_size_lex_n(+Min,+Max,-Rules)
%%
%%	Rules unifies with a conjunction of rules which defines the
%%	maxi/1 predicates for i in{Min...Max}. Used by gmax strategy.

max_size_lex_n(N,N,(Head :- Tail)) :-
	concatenate(max,N,FMaxn),
	concatenate('X',N,V),
	Head =.. [FMaxn,'$VAR'(V)],
	funct_n(max,'X',N,Size), % max(X1,...Xn)
	chain_ge(1,N,'X',Chain),    % X1>= X2,...,Xn-1 >= Xn
	conjoin(Size,Chain,Tail)
	.
max_size_lex_n(N1,N,Conj) :-
	N1 #< N,
	concatenate(max,N1,FMaxn),
	concatenate('X',N1,V),
	Head =.. [FMaxn,'$VAR'(V)],
	funct_n(max,'X',N,Size), % max(X1,...Xn)
	chain_ge(1,N,'X',Chain),    % X1>= X2,...,Xn-1 >= Xn
	conjoin(Size,Chain,Tail),
	N2 #= N1 + 1,
	conjoin((Head :- Tail),Conj1,Conj),
	max_size_lex_n(N2,N,Conj1)
	.

%%	max_size_lex(+NbBases, -Rules)
%%
%%	Rules unifies with the definition of max/NbBases and size/2
%%	predicates which are needed by the gmax strategy.

max_size_lex(N,Max) :-
	max_size_lex_n(1,N,Max_n),
	funct_n(max,'X',N,Size), % max(X1,...Xn)
	size2_n(1,N,'X','Y',Conj1), % size(X1,Y1),...,size(Xn,Yn)
	chain_ge(1,N,'X',Chain),    % X1>= X2,...,Xn-1 >= Xn
        all_op('!=',1,N,'Y',Neq),
	conjoin(Conj1,Chain,Conj2),
	conjoin(Conj2,Neq,Tail1),
	flatten_conjunction(Tail1,Tail),
	conjoin((Size :- Tail),Max_n,Max)
	.

%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	Miscellaneous rsf-related predicates

%%	max_rules(+Profile, ?S)
%%
%%	True if S is the size of the biggest base in the Profile.

max_rules(P,S) :-
	\+ var(P),
	max_rules(P,0,S)
	.

max_rules([],S,S).
max_rules([ic-_|P],S1,S2) :-
	max_rules(P,S1,S2)
	.
max_rules([_Name-KB|P],S1,S2) :-
	conjunct_size(KB,CurS),
	CurS > S1,
	max_rules(P,CurS,S2)
	.
max_rules([_Name-KB|P],S1,S2) :-
	conjunct_size(KB,CurS),
	CurS =< S1,
	max_rules(P,S1,S2)
	.
















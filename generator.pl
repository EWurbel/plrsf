%% -*- prolog -*-
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	Copyright 2012 Éric Würbel, LSIS-CNRS, Université du Sud
%%	Toulon-Var
%%
%%	This file is part of PLRsf-solver.
%%	PLRsf-Solver is free software: you can redistribute it and/or
%%	modify it under the terms of the GNU General Public License as
%%	published by the Free Software Foundation, either version 3 of
%%	the License, or (at your option) any later version.
%%
%%	PLRsf-Solver is distributed in the hope that it will be useful,
%%	but WITHOUT ANY WARRANTY; without even the implied warranty of
%%	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
%%	General Public License for more details.
%%
%%	You should have received a copy of the GNU General Public
%%	License along with Rsf-solver. If not, see
%%	<http://www.gnu.org/licenses/>.
%%
%%	PLRsf-Solver implements removed set fusion of
%%	knowledge bases represented by logic programs.
%%
%%	This module handles the generation of the ASP program which
%%	represents a profile (i.e. a multifile of knowledge bases).
%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-module(generator, [
		     init_profile/1,
		     reset_rule_atoms/1,
		     collect_rule_atoms/2,
		     get_rules/3,
		     erase_rules/1,
		     kbnames/1,

		     gen_atoms_htrules/2,
		     gen_atoms_asrules/2,
		     gen_profile_htrules/2,
		     gen_profile_asrules/2
		    ]).

:-use_module(logic).
:-use_module(asp).

:-dynamic kbnames/1.
:-dynamic rule/3.
:-volatile kbnames/1.
:-volatile rule/3.

%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	Common rules.
%%
%%	Predicates which are comon to both weak and strong merging
%%	operators.
%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%	collect_atoms(?Profile,?IAtoms,?OAtoms)
%	true if OAtoms is a set of atoms containing
%       the atoms in IAtoms union the atoms present in
%	Profile. Atoms are extended atoms in the sense of extended logic
%	programs, i.e. propositionnal atoms or their strong negation.
%
%	This predicate is common to the weak and strong modes.

collect_atoms([],A,A).
collect_atoms([_Name-Rules|KBs],Set,NewSet) :-
	collect_kb_atoms(Rules,Set,Set1),
	collect_atoms(KBs,Set1,NewSet)
	.

collect_kb_atoms((A,B),Set,NewSet) :-
	collect_kb_atoms(A, Set, Set1),
	collect_kb_atoms(B, Set1, NewSet)
	.
collect_kb_atoms((:-B),Set,NewSet) :-
        collect_kb_atoms(B,Set,NewSet)
	.
collect_kb_atoms((H :- B),Set,NewSet) :-
        collect_kb_atoms(H,Set,Set1),
	collect_kb_atoms(B,Set1,NewSet)
	.
collect_kb_atoms((not A),Set,NewSet) :-
	collect_kb_atoms(A, Set, NewSet)
	.
collect_kb_atoms(-A,Set,NewSet) :-
	atom(A),
	ord_add_element(Set,-A,NewSet)
	.
collect_kb_atoms(A,Set,NewSet) :-
	atom(A),
	ord_add_element(Set,A,NewSet)
	.



%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	Ht-models generation rules.
%%
%%	The following predicates allows the generation of the ht-models
%%	of a profile (a multiset of knowledge bases) or a knowledge
%%	base.
%%	A knowledge base (kb for short) is simply a program. It must
%%	also contains a special fact kbname/1 which allows to name the
%%	kb. This fact is not part of the program. It won't be accounted
%%	in the computations.
%%
%%	See the module profileio for more information about the
%%	structure of a profile and a kb.
%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%	gen_atoms_htrules(+Profile, AtomRules)
%%	Associate atoms of a profile with the rules representing them in
%%	the merging system.
gen_atoms_htrules(Profile, AtomRules) :-
	collect_atoms(Profile,[],Atoms),
	gen_atom_htrules_c(Atoms,Rules1),
	forbid_opposite_litterals(Atoms,Rules2),
	% represent the "false" atom used for constraints
	conjoin( ((1 // [rsffalse(h), -rsffalse(h)] // 1),
		  (1 // [rsffalse(t), -rsffalse(t)] // 1),
		  (:- rsffalse(h), -rsffalse(t)),
		  (:- rsffalse(t)), (:-rsffalse(h))),
		 Rules1,Rules3),
	conjoin(Rules3,Rules2,Rules),
	flatten_conjunction(Rules,AtomRules)
	.



%%	gen_atom_rules_c(?Atoms, ?Rules)
%%      True if rules represent the generation of HT-interpretations
%%	over the list of Atoms, using choice constucts.
gen_atom_htrules_c([],true).
gen_atom_htrules_c([-A|L], AtRules) :-
	nh(A,AH),
	nt(A,AT),
	gen_atom_htrules_c(L,Rules),
	conjoin((1 // [AT,-AT] // 1,
		 1 // [AH,-AH] // 1,
		 (:- AH, -AT)),Rules,AtRules)
	.
gen_atom_htrules_c([A|L], AtRules) :-
	A \= -_,
	h(A,AH),
	t(A,AT),
	gen_atom_htrules_c(L,Rules),
	conjoin((1 // [AT,-AT] // 1,
		 1 // [AH,-AH] // 1,
		 (:- AH, -AT)),Rules,AtRules)
	.

%%	forbid_opposite_literals(+Lits,-Rules)
%%	Rules is a set of rules allowing the mutual
%%	exclusion of the opposite atoms present in the
%%      Lits set.
forbid_opposite_litterals([],true).
forbid_opposite_litterals([-A|T],Rules) :-
	member(A,T),
	!,
	select(A,T,T1),
	h(A,AH),
	t(A,AT),
	nh(A,NAH),
	nt(A,NAT),
	forbid_opposite_litterals(T1,Rules1),
	conjoin(((:-AH,NAH),(:-AT,NAT)),Rules1,Rules)
	.
forbid_opposite_litterals([A|T],Rules) :-
	A \= -_,
	member(-A,T),
	!,
	select(-A,T,T1),
	h(A,AH),
	t(A,AT),
	nh(A,NAH),
	nt(A,NAT),
	forbid_opposite_litterals(T1,Rules1),
	conjoin(((:-AH,NAH),(:-AT,NAT)),Rules1,Rules)
	.
forbid_opposite_litterals([_|T],Rules) :-
	forbid_opposite_litterals(T,Rules).


%%	h(?Atom, ?Representation)
%%	True if AH is the 'here' tagged version of the atom A.
h(A, AH) :-
	atom(A),
	AH =.. [A,p,h]
	.

%%	t(?Atom, ?Representation)
%%	True if AH is the 'there' tagged version of the atom A.
t(A, AT) :-
	atom(A),
	AT =.. [A,p,t]
	.

%%	nh(?Atom, ?Representation)
%%	True if AH is the 'here' tagged version of the atom -A.
nh(A, AH) :-
	atom(A),
	AH =.. [A,n,h]
	.
%%	nt(?Atom, ?Representation)
%%	True if AH is the 'there' tagged version of the atom -A.
nt(A, AT) :-
	atom(A),
	AT =.. [A,n,t]
	.



%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	Profile generation


%%	gen_profile_htrules(?Profile, ?Profile_repr)
%%	associate a profile and its representation in the merging
%%	system. This representation consists in the rules ensuring
%%      the production of ht-models, except that rules from the
%%	KBs preventing model generation raise a spoiling atom instead
%%      of violating a constraint.
gen_profile_htrules([],true).
gen_profile_htrules([ic-Rules|KBs],Repr) :-
	gen_ht_rules(Rules,ICRepr),
	gen_profile_htrules(KBs,Repr1),
	conjoin(ICRepr,Repr1,Repr)
	.
gen_profile_htrules([Name-Rules|KBs],Repr) :-
	Name \= ic,
	gen_ht_rules(Name,Rules,KBRepr),
	gen_profile_htrules(KBs,Repr1),
	conjoin(KBRepr,Repr1,Repr)
	.

%%	gen_ht_rules(+Name,+Rules,-KBR)
%%	Associate a knowledge base and its representation in the
%%	merging system.
%%	This representation is a conjunction of rules allowing the
%%	generation of the HT-models of the KB, except that rules from
%%	the KB preventing model generation raise a spoiling atom instead
%%	of violating a constraint. The spoiling atom name is generated
%%	from the KB name
gen_ht_rules(Name,(A,B),Repr) :-
	gen_ht_rules(Name,A,R1),
	gen_ht_rules(Name,B,R2),
	conjoin(R1,R2,Repr).
gen_ht_rules(Name, (H :- B), HTRules) :-
	next_rule_atom(Name, RAtom),
	record_rule(Name, RAtom, (H :- B)),
	head('-',t,H,C1),
	posbody('+',t,B,C2),
	negbody('-',t,B,C3),
	conjoin(C1,C2,B1),
	conjoin(C3,B1,Body1),
	HTRule1 = (RAtom :- Body1),
	head('-',h,H,C4),
	posbody('+',h,B,C5),
	conjoin(C4,C5,B2),
	conjoin(C3,B2,Body2),
	HTRule2 = (RAtom :- Body2),
	conjoin(HTRule1,HTRule2,HTRules)
	.
gen_ht_rules(Name, (:- B), HTRules) :-
	next_rule_atom(Name, RAtom),
	record_rule(Name, RAtom, (:- B)),
	posbody('+',t,B,C1),
	negbody('-',t,B,C2),
	conjoin(-rsffalse(t),C1,B1),
	conjoin(C2,B1,Body1),
	HTRule1 = (RAtom :- Body1),
	posbody('+',h,B,C3),
	conjoin(-rsffalse(h),C3,B2),
	conjoin(C2,B2,Body2),
	HTRule2 = (RAtom :- Body2),
	conjoin(HTRule1,HTRule2,HTRules)
	.
gen_ht_rules(Name,Fact,HTRules) :-
	Fact \= (_,_),
	Fact \= (_ :- _),
	Fact \= (:- _),
	next_rule_atom(Name, RAtom),
	record_rule(Name, RAtom, Fact),
	head('-',t,Fact,C1),
	head('-',h,Fact,C2),
	HTRule1 = (RAtom :- C1),
	HTRule2 = (RAtom :- C2),
	conjoin(HTRule1,HTRule2,HTRules)
	.

%%	gen_ht_rules(+Rules,-HTRules)
%%	Associate a conjunction of rules with a conjunction of rules
%%	computing the HT-models.
gen_ht_rules((A,B),Repr) :-
	gen_ht_rules(A,R1),
	gen_ht_rules(B,R2),
	conjoin(R1,R2,Repr).
gen_ht_rules((H :- B), HTRules) :-
	head('-',t,H,C1),
	posbody('+',t,B,C2),
	negbody('-',t,B,C3),
	conjoin(C1,C2,B1),
	conjoin(C3,B1,Body1),
	HTRule1 = (:- Body1),
	head('-',h,H,C4),
	posbody('+',h,B,C5),
	conjoin(C4,C5,B2),
	conjoin(C3,B2,Body2),
	HTRule2 = (:- Body2),
	conjoin(HTRule1,HTRule2,HTRules)
	.
gen_ht_rules((:- B), HTRules) :-
	posbody('+',t,B,C1),
	negbody('-',t,B,C2),
	conjoin(-rsffalse(t),C1,B1),
	conjoin(C2,B1,Body1),
	HTRule1 = (:- Body1),
	posbody('+',h,B,C3),
	conjoin(-rsffalse(h),C3,B2),
	conjoin(C2,B2,Body2),
	HTRule2 = (:- Body2),
	conjoin(HTRule1,HTRule2,HTRules)
	.
gen_ht_rules(Fact,HTRules) :-
	Fact \= (_,_),
	Fact \= (_ :- _),
	Fact \= (:- _),
	head('-',t,Fact,C1),
	head('-',h,Fact,C2),
	HTRule1 = (:- C1),
	HTRule2 = (:- C2),
	conjoin(HTRule1,HTRule2,HTRules)
	.



head(Sign,S,(A ; B),Conjunct) :-
	head(Sign,S,A,C1),
	head(Sign,S,B,C2),
	conjoin(C1,C2,Conjunct)
	.
head(_,_,(not _),true).
head('-',S,-Atom,-NewAtom) :-
	Atom \= (_ ; _),
	Atom \= (not _),
	NewAtom =.. [Atom,n,S]
	.
head('-',S,Atom,-NewAtom) :-
	Atom \= (_ ; _),
	Atom \= (not _),
	Atom \= -_,
	NewAtom =.. [Atom,p,S]
	.
head('+',S,-Atom,NewAtom) :-
	Atom \= (_ ; _),
	Atom \= (not _),
	NewAtom =.. [Atom,n,S]
	.
head('+',S,Atom,NewAtom) :-
	Atom \= (_ ; _),
	Atom \= (not _),
	Atom \= -_,
	NewAtom =.. [Atom,p,S]
	.

posbody(Sign,S,(A , B),Conjunct) :-
	posbody(Sign,S,A,C1),
	posbody(Sign,S,B,C2),
	conjoin(C1,C2,Conjunct)
	.
posbody(_,_,(not _),true).
posbody('-',S,-Atom,-NewAtom) :-
	Atom \= (_ , _),
	Atom \= (not _),
	NewAtom =.. [Atom,n,S]
	.
posbody('-',S,Atom,-NewAtom) :-
	Atom \= (_ , _),
	Atom \= (not _),
	Atom \= -_,
	NewAtom =.. [Atom,p,S]
	.
posbody('+',S,-Atom,NewAtom) :-
	Atom \= (_ , _),
	Atom \= (not _),
	NewAtom =.. [Atom,n,S]
	.
posbody('+',S,Atom,NewAtom) :-
	Atom \= (_ , _),
	Atom \= (not _),
	Atom \= -_,
	NewAtom =.. [Atom,p,S]
	.

negbody(Sign,S,(A , B),Conjunct) :-
	negbody(Sign,S,A,C1),
	negbody(Sign,S,B,C2),
	conjoin(C1,C2,Conjunct)
	.
negbody(_,_,Atom,true) :-
	Atom \= (not _),
	Atom \= (_ , _).
negbody('-',S,(not -Atom),-NewAtom) :-
	NewAtom =.. [Atom,n,S]
	.
negbody('-',S,(not Atom),-NewAtom) :-
	Atom \= -_,
	NewAtom =.. [Atom,p,S]
	.
negbody('+',S,(not -Atom),NewAtom) :-
	NewAtom =.. [Atom,n,S]
	.
negbody('+',S,(not Atom),NewAtom) :-
	Atom \= -_,
	NewAtom =.. [Atom,p,S]
	.
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	Strong version generation rules.
%%
%%	The following predicates allows for the generation of the
%%	repesentation of a belief profile (a multiset of logic programs)
%%	in the strong removed sets merging system.
%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%	gen_atoms_asrules(+Profile, AtomRules)
%%	Associate atoms of a profile with the rules representing them in
%%	the merging system.
gen_atoms_asrules(Profile, AtomRules) :-
	collect_atoms(Profile,[],Atoms),
	gen_atom_asrules_c(Atoms,Rules1),
	auth_exclusion(Atoms,Rules2),
	conjoin(Rules1,Rules2,Rules3),
	flatten_conjunction(Rules3,AtomRules)
	.

%%	gen_atom_asrules_c(?Atoms, ?Rules)
%%      True if rules represent the generation of interpretations
%%	over the list of Atoms, using choice constucts.

gen_atom_asrules_c(Atoms,Rules) :-
	length(Atoms,L),
	as_forbid_opposite_lits(Atoms, OppRules),
	conjoin(1 // Atoms // L,
		OppRules, Rules)
	.

as_forbid_opposite_lits([],true).
as_forbid_opposite_lits([-L|Lits],OppRules) :-
	memberchk(L,Lits),
	select(L,Lits,Lits1),
	as_forbid_opposite_lits(Lits1,Rules),
	conjoin((:-L,-L),Rules,OppRules)
	.
as_forbid_opposite_lits([-L|Lits],OppRules) :-
	\+ memberchk(L,Lits),
	as_forbid_opposite_lits(Lits,OppRules)
	.
as_forbid_opposite_lits([L|Lits],OppRules) :-
	L \= -_,
	memberchk(-L,Lits),
	select(-L,Lits,Lits1),
	as_forbid_opposite_lits(Lits1,Rules),
	conjoin((:-L,-L),Rules,OppRules)
	.
as_forbid_opposite_lits([L|Lits],OppRules) :-
	\+ memberchk(-L,Lits),
	as_forbid_opposite_lits(Lits,OppRules)
	.

%%	auth_exclusion(?AuthAtoms,?ExclRules)
%%	True if ?AuthAtoms is a conjunction of auth/1 atoms and, for
%	each atom auth(X), a rule (:- X, auth(X)) is present inthe
%	conjonction of rules ExclRules.

auth_exclusion([-A],(:- -A, not auth(neg__(A)))).
auth_exclusion([A],(:- A, not auth(A))) :- A \= -_.
auth_exclusion([-A|L],((:- -A, not auth(neg__(A))),Conj)) :-
	auth_exclusion(L,Conj)
	.
auth_exclusion([A|L],((:- A, not auth(A)),Conj)) :-
	A \= -_,
	auth_exclusion(L,Conj)
	.



%%	gen_profile_asrules(?Profile, ?Profile_repr)
%%	associate a profile and its representation in the merging
%%	system. This representation consists in the rules ensuring
%%      the production of answer sets, except that rules from the
%%	KBs preventing model generation raise a spoiling atom instead
%%      of violating a constraint.
gen_profile_asrules([],true).
gen_profile_asrules([ic-Rules|KBs],Repr) :-
	gen_as_rules(Rules,ICRepr),
	gen_profile_asrules(KBs,Repr1),
	conjoin(ICRepr,Repr1,Repr)
	.
gen_profile_asrules([Name-Rules|KBs],Repr) :-
	Name \= ic,
	gen_as_rules(Name,Rules,KBRepr),
	gen_profile_asrules(KBs,Repr1),
	conjoin(KBRepr,Repr1,Repr)
	.

%%	gen_as_rules(+Name,+Rules,-KBR)
%%	Associate a Knowledge base with name Name and its
%	representation in the merging system. This representation is a
%	conjunction of rules allowing the generation of the answer sets
%	of the Knowledge base. The rules defeated by the current
%	interpretation generate a spoiling atom in the model (a "rule
%	atom").

gen_as_rules(Name,(A,B),Repr) :-
	% conjunction of rules
	gen_as_rules(Name,A,R1),
	gen_as_rules(Name,B,R2),
	conjoin(R1,R2,Repr)
	.
gen_as_rules(Name,(H :- B), ASRules) :-
	% head :- body rule
	next_rule_atom(Name, RAtom),
	record_rule(Name, RAtom, (H :- B)),
	conjoin((not H),B,RMBody1),
	flatten_conjunction(RMBody1,RMBody),
	RMRule = (RAtom :- RMBody),
	auth(H,AuthHead),
	auth(B,AuthBody),
	conjoin((not RAtom),AuthBody,AuthBody1),
	flatten_conjunction(AuthBody1,AuthBody2),
	AuthRule = (AuthHead :- AuthBody2),
	conjoin(RMRule,AuthRule,ASRules)
	.
gen_as_rules(Name, (:- B), ASRules) :-
	next_rule_atom(Name, RAtom),
	record_rule(Name, RAtom, (:- B)),
	RMRule = (RAtom :- B),
	auth(B,AuthBody),
	conjoin((not RAtom),AuthBody,AuthBody1),
	flatten_conjunction(AuthBody1,AuthBody2),
	AuthRule = (:- AuthBody2),
	conjoin(RMRule,AuthRule,ASRules)
	.
gen_as_rules(Name,Fact,ASRules) :-
	Fact \= (_,_),
	Fact \= (_ :- _),
	Fact \= (:- _),
	next_rule_atom(Name, RAtom),
	record_rule(Name, RAtom, Fact),
	RMRule = (RAtom :- (not Fact)),
	auth(Fact,AuthFact),
	AuthRule = (AuthFact :- (not RAtom)),
	conjoin(RMRule,AuthRule,ASRules)
	.


%%	gen_as_rules(+Rules,-KBR)
%%	Associate a set of integrity constraints and its
%	representation in the merging system. This representation is a
%	conjunction of rules allowing the generation of the answer sets
%	of the integrity constraints.

gen_as_rules((A,B),Repr) :-
	% conjunction of rules
	gen_as_rules(A,R1),
	gen_as_rules(B,R2),
	conjoin(R1,R2,Repr)
	.
gen_as_rules((H :- B), ASRule) :-
	% head :- body rule
	conjoin((not H),B,RMBody1),
	flatten_conjunction(RMBody1,RMBody),
	ASRule = (:- RMBody)
	.
gen_as_rules((:- B), (:- B)).
gen_as_rules(Fact,(:- not Fact)) :-
	Fact \= (_,_),
	Fact \= (_ :- _),
	Fact \= (:- _)
	.






%%	auth(?AAtoms,?Atoms)
%%	true if AAtoms is a conjunction of auth/1 atoms corresponding to
%	Atoms.

auth(true,true).
auth((A,B),(A1,B1)) :-
	auth(A,A1),
	auth(B,B1)
	.
auth(-A,auth(neg__(A))).
auth((not A), not B) :-
	auth(A, B)
	.
auth(A,auth(A)) :-
	A \= true,
	A \= (_, _),
	A \= -_,
	A \= (not _)
	.


%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	Global vars predicates
%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


next_value(Counter, Value) :-
	\+ var(Counter),
	nb_current(Counter,_),
	nb_getval(Counter, Value),
	Value1 is Value + 1,
	nb_setval(Counter, Value1)
	.
next_value(Counter, 1) :-
	\+ var(Counter),
	\+ nb_current(Counter,_),
	nb_setval(Counter, 2)
	.

%%	reset_rule_atoms(KBName)
%%	Resets the counter used for the generation of rule atoms.

reset_rule_atoms(KBName) :-
	nb_delete(KBName)
	.

next_rule_atom(KBName, Atom) :-
	next_value(KBName, Value),
	Atom =.. [rsf,KBName,Value]
	.

%%	collect_rule_atoms(+Profile,-RuleAtoms)
%%	Collect all rule atoms for a given profile.
collect_rule_atoms([],[]).
collect_rule_atoms([KBName-_|Profile],RuleAtoms) :-
	bagof(A,R^get_rules(KBName,R,A),KA),
	append(KA,RA,RuleAtoms),
	collect_rule_atoms(Profile,RA)
	.

%%	record_rule(+KBName, +Ratom, +Rule)
%%	records the association between a rule and its rule atom.
%%	This will be used later on to generate the result.
%%	We use the assert/1 mechanism in order to be fully non
%%	deerminist, i.e. to allow queries with all possible patterns of
%	instantiation of KBName, Ratom ans Rule.

record_rule(KBName, RAtom, Rule) :-
	assert(rule(KBName,RAtom,Rule))
	.

%%	get_rules(+KBName,-Rule,-Atom)
%%	True if the Rule corresponds to the rule atom Atom in the
%%	specified knowledge base. There is an implicit hypothesis
%%	that rules are not duplicated in a single knowledge base.
%%	This hypothesis is necessary for the case +Rule, -Atom.
get_rules(KBName, Rule, Atom) :-
	rule(KBName,Atom,Rule)
	.

%%	erase_rules(+KBName)
%%	Erases the rules for the given knowledge base.
erase_rules(KBName) :-
	\+ var(KBName),
	retractall(rule(KBName,_,_))
	.

%%	init_profile(+Profile)
%%	various initializations. Must be called before any predicate in
%%	this module.
init_profile(P) :-
        retractall(kbnames(_)),
	init_profile2(P),
	collect_kbnames(P,L),
	assert(kbnames(L))
	.


init_profile2([]).
init_profile2([Name - _|Profile]) :-
	reset_rule_atoms(Name),
	erase_rules(Name),
	init_profile2(Profile)
	.

collect_kbnames([],[]).
collect_kbnames([ic-_|Profile],L) :-
	collect_kbnames(Profile,L)
	.
collect_kbnames([Name-_|Profile],[Name|L]) :-
	collect_kbnames(Profile,L)
	.




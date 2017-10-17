%% -*- prolog -*-
/*
    Copyright Éric Würbel, LSIS-CNRS UMR7196, (2012-2017)

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

	This module defines logical formulae handling predicates.
*/

:-module(logic, [
		 conjoin/3,
		 n_conjoin/2,
		 apply_to_conjuncts/3,
		 apply_to_conjuncts/4,
		 flatten_conjunction/2,
		 conjunct_size/2
		]).

:-meta_predicate apply_to_conjuncts(?,2,?).
:-meta_predicate apply_to_conjuncts(?,3,?,?).

:- use_module(asp).

:- use_module(library(clpfd)).


%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	logic syntax manipulation predicates.
%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%	conjoin(?A, ?B, ?C)
%%
%%	C unifies with the conjunction of A and B. Conjonction is
%%	represented à la prolog, that is with a comma.
%%	(from Mark Stickel's PTTP)

conjoin(A,B,C) :-
        A == true ->
                C = B;
        B == true ->
                C = A;
        A == false ->
                C = false;
        B == false ->
                C = false;
        A == B ->
                C = A;
        (B = (B1,_), A == B1) ->
                C = B;
        (A = (_,A2), B == A2) ->
                C = A;
        %true ->
                C = (A , B).

%%	n_conjoin(?List, ?C)
%%
%%	unbounded arity version of conjoin/3.

n_conjoin([],true).
n_conjoin([C|L],Conj) :-
	conjoin(C,C1,Conj),
	n_conjoin(L,C1)
	.

%%	apply_to_conjuncts(?Wff,+P,?Wff1)
%%
%%	apply P/2 predicate to each conjunt in Wff and Wff1.
%%	That is, for all conjunct X,Y in Wff, call P(X,X1), P(Y,Y1), and
%%	then conjunct X1 and Y1 to build Wff1 (from Mark Stickel's PTTP)

apply_to_conjuncts(Wff,P,Wff1) :-
        Wff = (A , B) ->
                apply_to_conjuncts(A,P,A1),
                apply_to_conjuncts(B,P,B1),
                conjoin(A1,B1,Wff1);
        %true ->
                call(P,Wff,Wff1)
	.

%%	apply_to_conjuncts(?Wff,+P, ?Arg, ?Wff1)
%%
%%	Same as apply_to_conjuncts/3, but each call to P is of the form
%%	P(X,Arg,Y), where X is in Wff. See apply_to_conjuncts/3 for more
%%	info.

apply_to_conjuncts(Wff,P,Arg,Wff1) :-
        Wff = (A , B) ->
                apply_to_conjuncts(A,P,Arg,A1),
                apply_to_conjuncts(B,P,Arg,B1),
                conjoin(A1,B1,Wff1);
        %true ->
                call(P,Wff,Arg,Wff1)
	.

%%	flatten_conjunction(+Wff,-FWff)
%%
%%	FWff is unified with the flattened version of Wff.
%%	(from Mark Stickel's PTTP)

flatten_conjunction( Wff, FWff ) :-
	flatten_conjunction(Wff,true,FWff).

flatten_conjunction( Wff, AWff, FWff ) :-
	Wff = (Wff1,Wff2) ->
	      flatten_conjunction(Wff2,AWff,FWff1),
	      flatten_conjunction(Wff1,FWff1,FWff);
	AWff = true ->
	      FWff = Wff;
	%true ->
              FWff = (Wff,AWff)
	      .

%%	conjunct_size(C, S)
%%
%%	True if S is the size of the conjunction C. The conjunction
%	needs to be flat, eg : (r1, (r2, ...(r(n-1),rn)...))

conjunct_size((_,B),S) :-
	S #= S1 + 1,
	conjunct_size(B,S1)
	.
conjunct_size(R,1) :-
	R \= (_,_)
	.














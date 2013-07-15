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
%%	This module defines logical formulae manipulation predicates.
%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
%%	unbounded arity version of conjoin/3.

n_conjoin([],true).
n_conjoin([C|L],Conj) :-
	conjoin(C,C1,Conj),
	n_conjoin(L,C1)
	.

%%	apply_to_conjuncts(?Wff,+P,?Wff1)
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
%%	True if S is the size of the conjunction C. The conjunction
%	needs to be flat, eg : (r1, (r2, ...(r(n-1),rn)...))

conjunct_size((_,B),S) :-
	S #= S1 + 1,
	conjunct_size(B,S1)
	.
conjunct_size(R,1) :-
	R \= (_,_)
	.














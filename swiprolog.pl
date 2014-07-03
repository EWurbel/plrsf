%% -*-prolog-*-
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Copyright 2012-2014 Éric Würbel, LSIS-CNRS, Université de Toulon.
%%
%% This file is part of PLRsf-solver.
%% PLRsf-Solver is free software: you can redistribute it and/or
%% modify it under the terms of the GNU General Public License as
%% published by the Free Software Foundation, either version 3 of
%% the License, or (at your option) any later version.
%%
%% PLRsf-Solver is distributed in the hope that it will be useful,
%% but WITHOUT ANY WARRANTY; without even the implied warranty of
%% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
%% General Public License for more details.
%%
%% You should have received a copy of the GNU General Public
%% License along with Rsf-solver. If not, see
%% <http://www.gnu.org/licenses/>.
%%
%% PLRsf-Solver implements removed set fusion of
%% knowledge bases represented by logic programs.
%%
%% This module implements predicates which can be found on some
%% prolog systems but not on SwiProlog.
%% (actually, we should move all this in utils ...)
%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-module(swiprolog,[concatenate/3,
		    n_concatenate/2]).

:-use_module(utils,[chars_codes/2]).

:-use_module(library(charsio)).

%% concatenate(?A, ?B, ?C)
%% full flavored terms concatenation.
concatenate(String1,String2,String) :-
	full_name(String1,L1),
	full_name(String2,L2),
	append(L1,L2,L),
	name(String,L).


n_concatenate([T1,T2],R) :-
	concatenate(T1,T2,R).
n_concatenate([T1,T2|L],R) :-
	concatenate(T1,T2,T3),
	n_concatenate([T3|L],R)
	.

full_name(N,L) :-
	var(N), \+ var(L),
	chars_codes(C,L),
	read_term_from_chars(C,N,[end_of_term(eof)])
	.
full_name(N,L) :-
	\+ var(N),
	write_to_chars(N,L)
	.

%full_name((H :- T),L) :-
%	full_name(H,L1),
%	full_name(T,L2),
%	name(' :- ',OP),
%	append(L1,OP,L3),
%	append(L3,L2,L)
%	.
%full_name((H,T),L):-
%	full_name(H,L1),
%	full_name(T,L2),
%	name(',',OP),
%	append(L1,OP,L3),
%	append(L3,L2,L)
%	.
%full_name(A,L) :-
%	is_list(A),
%	name('[',OB),
%	name(']',CB),
%	full_list_name(A,L1),
%	append(OB,L1,L2),
%	append(L2,CB,L)
%	.
%full_name(A,L) :-
%	A =.. F,
%	func_name(F, L)
%	.
%
%full_list_name([],[]).
%full_list_name([A],L) :-
%	full_name(A,L)
%	.
%full_list_name([A|LL],L) :-
%	full_name(A,L1),
%	name(',',C),
%	append(L1,C,L2),
%	full_list_name(LL,L3),
%	append(L2,L3,L)
%	.
%
%func_name([A], L) :-
%	name(A, L)
%	.
%
%func_name([Functor,Arg], L) :-
%	current_op(_,T,Functor),
%	member(T,[fx,fy]),
%	name(Functor,Func),
%	args_names([Arg],LArg),
%	append(Func,LArg,L)
%	.
%func_name([Functor,Arg1,Arg2], L) :-
%	current_op(_,T,Functor),
%	member(T,[xfx,yfx,xfy,yfy]),
%	name(Functor,Func),
%	args_names([Arg1],LArg1),
%	args_names([Arg2],LArg2),
%	append(LArg1,Func,L1),
%	append(L1,LArg2,L)
%	.
%func_name([Functor|Args], L) :-
%	Args \= [],
%	\+ current_op(_,_,Functor),
%	name(Functor, LFunc),
%	args_names(Args,LArgs),
%	name('(',OP),
%	append(LFunc,OP, L1),
%	append(L1,LArgs,L2),
%	name(')',CP),
%	append(L2,CP,L)
%	.
%
%args_names([A],L) :-
%	var(A),
%	replace_variables(A,AV),
%	args_names([AV],L)
%	.
%args_names([A],L) :-
%	full_name(A,L)
%	.
%args_names([A|Args],L) :-
%	Args \= [],
%	full_name(A,LA),
%	args_names(Args,LArgs),
%	name(',',Comma),
%	append(LA,Comma,L1),
%	append(L1,LArgs,L)
%	.




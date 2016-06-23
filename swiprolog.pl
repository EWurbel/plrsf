%% -*-prolog-*-
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

    This module implements predicates which can be found on some
    prolog systems but not on SwiProlog.
    (actually, we should move all this in utils ...)
*/

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




%% -*-prolog-*-
/*
    Copyright 2012-2014 Éric Würbel, LSIS-CNRS, Université de Toulon.

    This file is part of PLRsf-solver.
    PLRsf-Solver is free software: you can redistribute it and/or
    modify it under the terms of the GNU General Public License as
    published by the Free Software Foundation, either version 3 of
    the License, or (at your option) any later version.

    PLRsf-Solver is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
    General Public License for more details.

    You should have received a copy of the GNU General Public
    License along with Rsf-solver. If not, see
    <http://www.gnu.org/licenses/>.

    PLRsf-Solver implements removed set fusion of
    knowledge bases represented by logic programs.

    Various useful predicates.
*/

:-module(utils,[
		error/2,
		error/1,
		chars_codes/2,
		integer_enum/3,
		integer_enuml/3
	       ]).

:-use_module(library(clpfd)).


%%	error(+Msg)
%
%	Writes an error message ont the user_error stream and throws a
%	plrsf_exception with the same message as argument.

error(Msg) :-
	write(user_error,Msg),
	throw(plrsf_exception(Msg))
	.

%%	error(+Fmt, +Args)
%
%	Formats a message, writes it ont the user_error stream, then
%	throws a plrsf_exception with the same formatted message as
%	argument.

error(Fmt, Args) :-
	format(user_error,Fmt,Args),
	format(atom(A),Fmt,Args),
	throw(plrsf_exception(A))
	.

%%	char_codes (?Chars, Codes)
%
%	From lists of chars to lists of codes.

chars_codes([],[]).
chars_codes([Ch|L1],[Co|L2]) :-
	char_code(Ch, Co),
	chars_codes(L1,L2)
	.

%%	integer_enum(?Min, ?Max, ?List)
%
%	List is a list of consecutive integers from Min to Max
%	(inclusive).

integer_enum(V, V, [V]).
integer_enum(Min, Max, [Min|L]) :-
	Min #< Max,
	Min1 #= Min+1,
	integer_enum(Min1,Max,L)
	.

%%	integer_enuml(?Min, ?Max, ?List)
%
%	List is a list of singleton lists containing consecutive
%	integers from Min to Max (inclusive).

integer_enuml(V, V, [[V]]).
integer_enuml(Min, Max, [[Min]|L]) :-
	Min #< Max,
	Min1 #= Min+1,
	integer_enuml(Min1,Max,L)
	.















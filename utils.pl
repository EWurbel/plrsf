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















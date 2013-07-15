:-module(utils,[
		error/2,
		error/1,
		chars_codes/2,
		integer_enum/3,
		integer_enuml/3
	       ]).

:-use_module(library(clpfd)).


%% Writes an error message
error(Msg) :-
	write(user_error,Msg),
	throw(plrsf_exception(Msg))
	.
error(Fmt, Args) :-
	format(user_error,Fmt,Args),
	format(atom(A),Fmt,Args),
	throw(plrsf_exception(A))
	.

%%	from lists of chars to lists of codes.
chars_codes([],[]).
chars_codes([Ch|L1],[Co|L2]) :-
	char_code(Ch, Co),
	chars_codes(L1,L2)
	.


integer_enum(V, V, [V]).
integer_enum(Min, Max, [Min|L]) :-
	Min #< Max,
	Min1 #= Min+1,
	integer_enum(Min1,Max,L)
	.
integer_enuml(V, V, [[V]]).
integer_enuml(Min, Max, [[Min]|L]) :-
	Min #< Max,
	Min1 #= Min+1,
	integer_enuml(Min1,Max,L)
	.















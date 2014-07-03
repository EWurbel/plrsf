%% -*- prolog -*-
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Copyright 2012-2014 Éric Würbel, LSIS-CNRS, Université de
%% Toulon
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
%% This module defines predicates for handling the loading of the belief
%% profiles.
%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-module(profileio,[
		    load_profile/2,
		    write_clauses/2,
		    write_conjunct/2,
		    read_wff_loop/3
		   ]).

:-use_module(utils).
:-use_module(logic,[conjoin/3]).
:-use_module(asp).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% IO pedicates

%%	load_profile(+File_list, -Profile).
%%	the resulting profile is list of pairs kb-rules
%%	with kb being the knowledge base name and rules being the
%%	conjunction of the rules in the knowledge base.
%%	the special name 'ic' i used to identify the integrity
%%	constraints.

load_profile([],[]).
load_profile([File|Files],[KBName-KB|Profile]) :-
	load_kb(File,KBName-KB),
	(var(KBName) ->
	    error('no KB name (i.e. kbname/1 atom) found in ~w~n', [File]);
	    true),
	load_profile(Files,Profile)
	.

%%	load_kb(+Kb_file,-KBName,-KB)
load_kb(File,KBName-Wff) :-
	exists_file(File),
        open(File,read,Stream),
        read_wff_loop(Stream,KBName,Wff),
        close(Stream)
	.
load_kb(File, _) :-
	\+ exists_file(File),
	error('~w: not found~n',[File])
	.



read_wff_loop(Stream,KBName,Wff) :-
        read_term(Stream,Wff1,[module(asp)]),
        (Wff1 == end_of_file ->
                   Wff = true;
	Wff1 = kbname(KBName) ->
	    read_wff_loop(Stream,KBName,Wff);
         %true               ->
	    read_wff_loop(Stream,KBName,Wff2),
	    conjoin(Wff1,Wff2,Wff))
	.

write_clauses(Conjunct, File) :-
	open(File,write,Stream),
	write_conjunct(Conjunct,Stream),
	close(Stream)
	.

write_conjunct((A, B),Stream) :-
	!,
	write_conjunct(A,Stream),
	write_conjunct(B,Stream)
	.
write_conjunct(R,Stream) :-
	write_term(Stream,R,[max_depth(0),numbervars(true),portray(true),module(asp)]),
	put(Stream,'.'),
	nl(Stream)
	.








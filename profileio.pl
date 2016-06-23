%% -*- prolog -*-
%%
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

    This module defines predicates which loads the belief profiles and
    writes the results.
*/


%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-module(profileio,[
	     load_profile/2,
	     write_clauses/2,
	     write_conjunct/2,
	     read_wff_loop/3,
	     write_clauses_to_atom/2,
	     write_profile_to_atoms/2
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

write_profile_to_atoms([],[]).
write_profile_to_atoms([Name-Conjunct|KBs], [Name-Atom|ATs]) :-
	write_clauses_to_atom(Conjunct, Atom),
	write_profile_to_atoms(KBs, ATs)
	.

write_clauses_to_atom(Conjunct, Atom) :-
	phrase(wca(Conjunct), Codes),
	atom_codes(Atom, Codes).

wca(Conjunct, In, Tail) :-
	with_output_to(codes(In, Tail), wrconjunct(Conjunct))
	.

wrconjunct(Conjunct) :-
	current_output(S),
	write_conjunct(Conjunct, S)
	.





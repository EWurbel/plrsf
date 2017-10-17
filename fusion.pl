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

*/

%% written for swi-prolog

:-use_module(logic,[
		    conjoin/3,
		    flatten_conjunction/2
		   ]).
:-use_module(asp,[run/2,
		  run/3,
		  op(900,fy,'#minimize')
		 ]).
:-use_module(profileio,[
			load_profile/2,
			write_clauses/2,
			write_conjunct/2
		       ]).
:-use_module(strategy).
:-use_module(generator).
:-use_module(utils).

:-use_module(library(clpfd)).
:-use_module(library(optparse)).

%%	transition to swi-prolog 7.2 strings

:-multifile check:valid_string_goal/1.
:-multifile error:has_type/2.

check:valid_string_goal(utils:error(S)) :- string(S).
check:valid_string_goal(utils:error(S,_)) :- string(S).

%%	Command line options specification.

opt_spec([
	  [
	   opt(clasppath), default(path(clingo)),
	   shortflags([c]), longflags(['clasp-path']),
	   help([ 'clasp path. Accepted values are either a pathname, relative'
		, 'or absolute, or a term of the form path(exe), where exe'
		, 'is the name of the executable. The executable is then'
		, 'searched among the directories specified in the PATH'
		, 'environment variable.'])
	  ],
	  [
	   opt(claspver), type(integer), default(4),
	   shortflags([v]), longflags(['clasp-ver']),
	   help([ 'clasp version. Accepted values are 3 and 4. Default is 4,'
		, 'meaning that the version of clasp is 4 or up. Aggregate'
		, 'litterals and choice constructs have a different syntax'
		, 'depending on the version number.'])
	  ],
	  [
	   opt(file), type(atom), default('user_output'),
	   shortflags([o]), longflags(['output']),
	   help([ 'output destination. This can be either a file name or the atom'
		, 'user_output, which stands for standard output.'])
	  ],
	  [
	   opt(mode), type(atom), default(strong),
	   shortflags([m]), longflags(['mode']),
	   help([ 'Potential reoved sets mode:'
		, '  weak:	weak potential removed sets (based on SE models)'
		, '  strong:	strong potendtial removed sets (based on answer sets)'])
	  ],
	  [
	   opt(strategy), type(atom), default(sigma),
	   shortflags([s]), longflags(['strategy']),
	   help([ 'merging strategy, one of'
		, '  sigma:   sigma strategy'
		, '  card:    card strategy'
		, '  max:     max strategy'
		, '  gmax:    gmax strategy'
		, '  inclmin: inclusion-minimal potential removed sets'
		, '  all:     all potential removed sets'])
	  ],
	  [
	   opt(results), type(atom), default(all),
	   shortflags([r]), longflags(['results']),
	   help([ 'requested results, one of '
		, '  all:    all belief bases resulting from the'
		, '          merging'
		, '  arsets: only print the atoms characterizing the removed sets.'
		, '          (debugging purpose mainly)'
		, '  rsets:  all removed sets.'])
	  ],
	  [
	   opt(outprog), type(atom), default('none'),
	   shortflags([p]), longflags(['program-output']),
	   help([ 'ASP program output, one of '
		, '  none:        program is temporary.'
		, '  user_output: ASP program is written on standard output.'
		, '  ATOM:        ASP program is written to the file whose '
		, '               name is ATOM.'])
	  ]
	 ]).

%%	error library (used by optparse) seem to not define this type,
%%	resulting in an unusability of the "term" type.

error:has_type(term, X)	  :- compound(X).
error:has_type(term, X)	  :- atom(X).
error:has_type(term, X)	  :- atomic(X).


%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	Main predicate

go :-
	current_prolog_flag(argv, [_|Args]),
%	 Args = ['--results', arsets, '--clasp-ver', '3',
%	 '--clasp-path',
%	 'path(\'/home/wurbel/\')','test/ex12-1.pl', 'test/ex12-2.pl'],
				% output file (default standard output)
	nb_setval(file,user_output),
				% default strategy (default sigma)
	nb_setval(strategy,sigma),
	                        % default interpretation of results :
				% generate all programs
	nb_setval(results,all),
				% default mode : strong potential removed sets
	nb_setval(mode,strong),
	nb_setval(outprog,none),
	nb_setval(claspver, 4),
	nb_setval(clasppath, path(clingo)),
	process_args(Args,InputFiles),
	print_start_state(InputFiles),
	(InputFiles = [] ->
	    error("no input files");
	    true),
				% file name for merging program generation
	tmp_file(plrsf,TmpFile),
	load_profile(InputFiles, Profile),
	generate(Profile,TmpFile),
	run_asp(TmpFile,Results),
	result_dir(InputFiles,Dir),
	result_name(Dir,Name),
	nb_getval(results,RType),
	interpret(Results,Name,RType)
	.

%%	run_rsf(+Strat, +Mode, +ResOpt, +Profile, -Results)
%
%	Main predicate for external handling (e.g. webserver). Run the
%	PlRSF fusion engine on the Profile, with specified Mode (either
%	weak or strong), using strategy Strat (sigma, card, max, gmax,
%	inclmin, all). Results is a list, which content depedents of the
%	ResOpt value. If ResOpt unifies with `all', Result is a list of
%	belief bases (programs) which are the possible results of the
%	merging operation. If ResOpt unifies with arsets then Results is
%	a list of sets of spoiling atoms representing the removed sets
%	according to the specified strategy. Finally, if ResOpt unifies
%	with rsets, Results is the list of removed sets according to the
%	specified strategy.

run_rsf(Strat, Mode, ResOpt, Profile, Results) :-
				% no program outpout.
	nb_setval(outprog,none),
	nb_setval(strategy,Strat),
	nb_setval(mode,Mode),
	nb_setval(results,ResOpt),
	nb_setval(claspver, 4),
	nb_setval(clasppath, path(clingo)),
	tmp_file(plrsf,TmpFile),
	generate(Profile,TmpFile),
	run_asp(TmpFile,Res),
	gather(Res,ResOpt,Results)
	.


%%	test starting predicate

test_rsf(Filenames,Strategy,Mode,RType) :-
				% output file (default standard output)
	nb_setval(file,user_output),
				% default strategy (default sigma)
	nb_setval(strategy,Strategy),
	                        % default interpretation of results :
				% generate all programs
	nb_setval(mode,Mode),
	nb_setval(results,RType),
	nb_setval(claspver, 4),
	nb_setval(clasppath, path(clingo)),
	nb_setval(outprog,none),
	tmp_file(plrsf,TmpFile),
	load_profile(Filenames,Profile),
	generate(Profile,TmpFile),
	run_asp(TmpFile,Results),
	result_dir(Filenames,Dir),
	result_name(Dir,Name),
	interpret(Results,Name,RType)
	.

%%	print_start_state(+InputFiles)
%
%	Writes on the standard output the state of all options and the
%	files given as arguments to the program.

print_start_state(IFiles) :-
	write('starting plrsf with:'), nl,
	write('\tInput Files: '), write(IFiles), nl,
	nb_getval(mode,F),
	write('\tMerging mode: '), write(F), nl,
	nb_getval(strategy,S),
	write('\tMerging strategy: '), write(S), nl,
	nb_getval(results,R),
	write('\tResults interpretation: '), write(R), nl,
	nb_getval(file,O),
	write('\tOutput: '), write(O), nl
	.

%%	process_args(+Args,-Files)
%
%       Parse command line arguments.
%
%	Appart from options, arguments consists in a list of input
%	files. Each input file represents a knowledge base of the
%	profile. It must contain a fact kbname/1, which names the
%	knowledge base. By convention, kbname(ic) represents the
%	integrity constraints (which implicitely means that if there is
%	no base containing kbname(ic), we deal with natural merging).

process_args(Args,Files) :-
	opt_spec(Specs),
	opt_parse(Specs,Args,Opts,Files,[output_functor(opt)]),
	%% check
	init_clasppath_opt(Opts),
	init_claspver_opt(Opts),
	init_file_opt(Opts),
	init_mode_opt(Opts),
	init_strategy_opt(Opts),
	init_results_opt(Opts),
	init_outprog_opt(Opts)
	.

%%	init_clasppath_opt(+Opts)
%
%	Check and sets the clasp path option.

init_clasppath_opt(Opts) :-
	member(opt(clasppath, V), Opts),
	!,
	(   V = file(F)
	->  true
	;   V = F
	),
	nb_setval(clasppath, F)
	.


%%	init_claspver_opt(+Opts)
%
%	Check and sets the clasp version option.
%
%	Throws a plrsf_exception if the version is unknown.

init_claspver_opt(Opts) :-
	member(opt(claspver,V), Opts),
	member(V, [3,4]),
	!,
	nb_setval(claspver, V)
	.
init_claspver_opt(Opts) :-
	member(opt(claspver,V), Opts),
	error("unknown clasp version: ~w~n", [V])
	.

%%	init_file_opt(+Opts)
%
%	Sets the output file.

init_file_opt(Opts) :-
	member(opt(file,V), Opts),
	nb_setval(file, V)
	.

%%	init_strategy_opt(+Opts)
%
%       check and sets the merging strategy.
%
%	Throws a plrsf_exception if the strategy is unknown.

init_strategy_opt(Opts) :-
	member(opt(strategy,V), Opts),
	member(V,[sigma, card, max, gmax, inclmin, all]),
	!,
	nb_setval(strategy, V)
	.
init_strategy_opt(Opts) :-
	member(opt(strategy, V), Opts),
	error("unknown strategy:  ~w~n", [V])
	.

%%	init_mode_opt(+Opts)
%
%       Check and sets the merging mode (weak or strong).
%
%	Throws a plrsf_exception if the specified merging mode is
%	unknown.

init_mode_opt(Opts) :-
	member(opt(mode,V),Opts),
	member(V,[weak,strong]),
	!,
	nb_setval(mode,V)
	.
init_mode_opt(Opts) :-
	member(opt(mode,V),Opts),
	error("unknown mode:  ~w~n", [V])
	.

%%	init_outprog_opt(+Opts)
%
%       Set the output program name.

init_outprog_opt(Opts) :-
	member(opt(outprog,V),Opts),
	nb_setval(outprog,V)
	.

%%	init_results_opt(+Opts)
%
%       Check and set the results option.
%
%       Throws a plrsf_exception if the result type is unknown.

init_results_opt(Opts) :-
	member(opt(results,V),Opts),
	member(V,[all,arsets,rsets]),
	!,
	nb_setval(results,V)
	.
init_results_opt(Opts) :-
	member(opt(results,V),Opts),
	error("unknown results request:  ~w~n", [V])
	.

%%	result_dir(+Profile,-Dir)
%
%       Get the directory of the profile.

result_dir([F|_],Dir) :-
	file_directory_name(F,Dir)
	.

%%	result_name(+Dir,-Name)
%
%	Compute the base name of the result files.

result_name(_,user_output):-
	catch(nb_getval(file,user_output),_,fail),
	!
	.
result_name(Dir,Name) :-
	catch(nb_getval(file,OBase),_,fail),
	!,
	atomic_list_concat([Dir,'/',OBase],Name1),
	prolog_to_os_filename(Name1,Name)
	.
result_name(Dir,Name) :-
	atomic_list_concat([Dir,'/','plrsf_result'],Name1),
	prolog_to_os_filename(Name1,Name)
	.


%%	run_asp(+TmpFile,-Results)
%
%	Run asp solver on TmpFile and unify Results with the results of
%	the run.

run_asp(TmpFile, Results) :-
	nb_getval(strategy,all), !,
	run(TmpFile,Results)
	.
run_asp(TmpFile, Results) :-
	nb_getval(strategy,inclmin), !,
	run(TmpFile,Results,[opt(inclmin)])
	.
% TODO: autoriser les deux options (voirs les commentaires dans
% post_process/2 dans asp.pl

%run_asp(TmpFile, Results) :-
%	nb_getval(strategy,max), !,
%	run(TmpFile,Results,[opt(prog),opt(inclmin)])
%	.
%run_asp(TmpFile, Results) :-
%	nb_getval(strategy,gmax), !,
%	run(TmpFile,Results,[opt(prog),opt(inclmin)])
%	.
run_asp(TmpFile, Results) :-
	run(TmpFile,Results,[opt(prog)])
	.



/*
	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	Main generation process

	Notes ont the generation:
	========================

	Prolog and ASP having a ver close syntax, the generation is
	quite easy. The construction of rules rely to a great extent on
	the prolog unification mechanism and term representation.
	However, there are a few exceptions :

	the curly brackets construction cannot be represented directly by
	a prolog construct. As a consequence, cardinality literals,
	reprensented as "Min { ... } Max" in ASP systems, will be
	represented here as Min // ... // Max.

	For optimization statements, we only need the [] notation, not
	the {} one, so we have no problem at all.
*/

%%      generate(+IFiles, +OFile)
%
%       generates the program which computes the removed sets.
%       IFiles is a list of input file names, OFile an output file name.

generate(Profile, OFile) :-
	init_profile(Profile),
	pre(Profile,NProfile),
	% generate the atoms representation.
	gen_atoms_rules(NProfile,AtRepr),
	% generate the profile representation.
	gen_profile_rules(NProfile,ProfRepr),
	subtract(NProfile,[ic-_],StratProfile),
	nb_getval(strategy,S),
	% generate the strategy
	gen_strategy(S,StratProfile,StratRepr),
	conjoin(AtRepr,ProfRepr,Repr1),
	conjoin(Repr1,StratRepr,Repr2),
	flatten_conjunction(Repr2, Repr),
	write_clauses(Repr, OFile),
	output_prog(Repr)
	.

%%	gen_atoms_rules(+Profile, -AtomRules)
%
%	Associate atoms of a profile with the rules representing them in
%	the merging system.

gen_atoms_rules(Profile,Representation) :-
	nb_getval(mode,weak),
	gen_atoms_htrules(Profile,Representation)
	.
gen_atoms_rules(Profile,Representation) :-
	nb_getval(mode,strong),
	gen_atoms_asrules(Profile,Representation)
	.

%%	gen_profile_rules(+Profile, -ProfRepr)
%
%	Generate the ASP rules representing the input belief profile.

gen_profile_rules(Profile,ProfRepr) :-
	nb_getval(mode,weak),
	gen_profile_htrules(Profile,ProfRepr)
	.
gen_profile_rules(Profile,ProfRepr) :-
	nb_getval(mode,strong),
	gen_profile_asrules(Profile,ProfRepr)
	.

%%	output_prog(+Repr)
%
%       Write the conjunction of rules if it has been requested by
%	option outporog.
%
%	!!! CUT !!!

output_prog(_) :-
	nb_getval(outprog,none),
	!
	.
output_prog(Repr) :-
	nb_getval(outprog,user_output),
	!,
	write_conjunct(Repr,user_output)
	.
output_prog(Repr) :-
	nb_getval(outprog,File),
	!,
	write_clauses(Repr,File)
	.


/*
	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	Results interpretation
	Several possibilities :

	1. generate all possible programs.
	   ==============================

	For each removed set, compute the resulting program. The result
        of the merging operation can be considered to be the union of
	the models of the program.

	2. print each removed set
	   ======================

	User will then be able to submit one of these removed set
	to the rsf-generate program, who will generate the corresponding
	ASP program.

	3. union possible ht-models, generate canonical program
	   ====================================================

	Pros : no choice to be made
	Cons : the generated program is no longer an extended program
	       (i.e. it is disjunctive, moreover is it a GLP).

*/



interpret(Results,BaseName,all) :-
	write_programs(Results,BaseName,0)
	.
interpret(Results,BaseName,arsets) :-
	write_arsets(Results,BaseName,0)
	.
interpret(Results,BaseName,rsets) :-
	gather_rsets(Results,RSets),
	write_rsets(RSets,BaseName,0)
	.

%%	gather(+Results, +Opt, -Output)
%
%	Gather the resutls according to the output option Opt. This
%	gives more flexibility to applications, e.g. to build a web
%	server demo.

gather(Results,all,Out) :-
	gather_programs(Results,Out)
	.
gather(Results,arsets,Out) :-
	gather_arsets(Results,Out)
	.
gather(Results,rsets,Out) :-
	gather_rsets(Results,Out)
	.


%%	gather_arsets(+Results,-Output)
%
%	generate all the the removed sets, only outputting
%	rsf/2 atoms

gather_arsets(Results,RSets) :-
	collect_rsets(Results,[],RSets)
	.

%%	gather_rsets(+Results,-Output)
%
%	generate all the the removed sets

gather_rsets(Results,RSets) :-
	collect_rsets(Results,[],ARSets),
	arsets_to_rsets(ARSets, RSets)
	.

%%	gather_programs(+Results,-Output)
%
%       Generate all the programs corresponding to the result
%	(i.e. the different removed sets).

gather_programs(Results,Programs) :-
	collect_rsets(Results,[],ARSets),
	findall(F/A,get_rules(_,F,A),FAList),
	arsets_to_programs(ARSets,Programs,FAList)
	.

%%	write_arsets(+Results,+BaseName,+Counter)
%
%	Output all the the removed sets, only outputting
%	rsf/2 atoms

write_arsets(Results,BaseName,Counter) :-
	collect_rsets(Results,[],RSets),
	output_arsets(RSets,BaseName,Counter)
	.
%%	write_rsets(+Results,+BaseName,+Counter)
%
%	Output all the the removed sets

write_rsets(RSets,BaseName,Counter) :-
	output_rsets(RSets,BaseName,Counter)
	.

%%	write_programs(+Results,+BaseName,+Counter)
%
%       Output all the programs corresponding to the result
%	(i.e. the different removed sets). Base name is the base of the
%	generated filenames. Counter is used to number the output files.

write_programs(Results,BaseName,Counter) :-
	collect_rsets(Results,[],RSets),
	wprograms(RSets,BaseName,Counter)
	.

%%	collect_rsets(+Results,+IRSets,-ORSets)
%
%	collect the removed sets, eliminating duplicates.

collect_rsets([],R,R).
collect_rsets([Res|L],IRsets,ORsets) :-
	keep_rule_atoms(Res,RAtoms),
	sort(RAtoms,SRAtoms),
	(   \+ member(SRAtoms,IRsets) ->
	    collect_rsets(L,[SRAtoms|IRsets],ORsets);
	    collect_rsets(L,IRsets,ORsets) )
	.


%%	keep_rule_atoms(+RSet,-RAtoms).
%
%	Keep only the rule atoms of a removed set.

keep_rule_atoms([],[]).
keep_rule_atoms([rsf(K,N)|L1],[rsf(K,N)|L2]) :-
	keep_rule_atoms(L1,L2)
	.
keep_rule_atoms([A|L1],L2) :-
	A \= rsf(_,_),
	keep_rule_atoms(L1,L2)
	.

%%	arsets_to_rsets(+ARSets, -RSets)
%
%	From sets of atoms representing removed sets to removed sets.

arsets_to_rsets([],[]).
arsets_to_rsets([ARSet|L1],[SRSet|L2]) :-
	arset_to_rset(ARSet,RSet),
	sort(RSet,SRSet),
	arsets_to_rsets(L1,L2)
	.
arset_to_rset([],[]).
arset_to_rset([A|L1],[F|L2]) :-
	get_rules(_,F,A),
	arset_to_rset(L1,L2)
	.

%%	arsets_to_bases(+ARSets,-Bases, +FAList)
%
%	From sets of atoms representing removed sets to belief bases
%	using the given formula/FormulaAtom list.

arsets_to_programs([],[],_).
arsets_to_programs([ARSet|L1],[Prog|L2],FAList) :-
	arset_to_program(ARSet,Prog,FAList),
	arsets_to_programs(L1,L2,FAList)
	.

arset_to_program(_,[],[]) :- !.
arset_to_program(Atoms,[F|L2],[F/A|FAList]) :-
	\+ var(A),
	\+ memberchk(A,Atoms),
	!,
	arset_to_program(Atoms,L2,FAList)
	.
arset_to_program(Atoms,[F|L2],[F/A|FAList]) :-
	var(A), % ic formulae have no formula atoms
	!,
	arset_to_program(Atoms,L2,FAList)
	.
arset_to_program(Atoms,L2,[_|FAList]) :-
	arset_to_program(Atoms,L2,FAList)
	.

%%	output_arsets(+RSets,+Filename,+Counter)
%
%	Output the rsf/2 predictes defining the removed sets in the
%	collection RSets. Filename is either a file name to write to, or
%	the atom user_output, which represents the standard output.
%	Counter is the starting value of a counter which indexes the
%	output.

output_arsets([],_,_).
output_arsets([RSet|L],user_output,Counter) :-
	write('==== Removed set '), write(Counter), write(' =========================='), nl,
	write_aset(RSet,user_output),
	Counter1 #= Counter + 1,
	output_arsets(L,user_output,Counter1)
	.
output_arsets([RSet|L],Base,Counter) :-
	atomic_list_concat([Base,'_',Counter,'.pl'],File),
	open(File,write,S),
	write_aset(RSet,S),
	Counter1 #= Counter + 1,
	output_arsets(L,Base,Counter1)
	.

%%	output_rsets(+RSets,+Filename,+Counter)
%
%	Output the removed sets in the collection RSets. Filename is
%	either a file name to write to, or the atom user_output, which
%	represents the standard output. Counter is the starting value of
%	a counter which indexes the output.

output_rsets([],_,_).
output_rsets([RSet|L],user_output,Counter) :-
	write('==== Removed set '), write(Counter), write(' =========================='), nl,
	write_rset(RSet,user_output),
	Counter1 #= Counter + 1,
	output_rsets(L,user_output,Counter1)
	.
output_rsets([RSet|L],Base,Counter) :-
	atomic_list_concat([Base,'_',Counter,'.pl'],File),
	open(File,write,S),
	write_rset(RSet,S),
	Counter1 #= Counter + 1,
	output_rsets(L,Base,Counter1)
	.

%%	wprograms(+Rset,+Basenme, +Counter)
%
%	output programs for all removed sets.

wprograms([],_,_).
wprograms([RSet|L],user_output,Counter) :-
	write('==== Base '), write(Counter), write(' =========================='), nl,
	wprogram(RSet,user_output),
	Counter1 #= Counter + 1,
	wprograms(L,user_output,Counter1)
	.
wprograms([RSet|L],Base,Counter) :-
	atomic_list_concat([Base,'_',Counter,'.pl'],File),
	open(File,write,S),
	wprogram(RSet,S),
	close(S),
	Counter1 #= Counter + 1,
	wprograms(L,Base,Counter1)
	.

%%	wprogram(RSet, Stream)
%
%	Write the program corresponding to the given remove set on the
%	stream.

wprogram(RSet,Stream) :-
	get_rules(_,Rule,RA),
	% formulae from IC do not have formula atoms,
	% that's what the var/1 is for. For knowldege bases,
	% we check a that the formula atom is not in the removed set.
	(   \+ member(RA, RSet) ; var(RA)   ),
	write_term(Stream,Rule,[module(asp)]),
	write(Stream,'.'),nl(Stream),
	fail
	.
wprogram(_,_).

%%	write_aset(+RSet,+Stream)
%
%	Write atom set on stream

write_aset([],_).
write_aset([A|L],S) :-
	write_term(S,A,[]),
	write(S,'.'), nl(S),
	write_aset(L,S)
	.

%%	write_rset(+RSet,+Stream)
%
%	write given removed et on stream.

write_rset([],_).
write_rset([Rule|L],S) :-
	write_term(S,Rule,[module(asp)]),
	write(S,'.'),nl(S),
	write_rset(L,S)
	.



%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	Miscelaneous utilitary predicates.


portray_list([]).
portray_list([C|L]) :-
	portray_clause(C),
	portray_list(L)
	.

portray_conjunct((A,B)) :-
	portray_conjunct(A),
	portray_conjunct(B)
	.
portray_conjunct(C) :-
	C \= (_,_),
	portray_clause(C)
	.

%%	Handle internal representations
portray(Min // BList // Max) :-
	% cardinality literals representation
	nb_getval(claspver, 3),
	write_term(Min, [max_depth(0), numbervars(true)]),
	write('{'),
	plist(BList),
	write('}'),
	write_term(Max, [max_depth(0), numbervars(true)])
	.
portray(Min // BList // Max) :-
	% cardinality literals representation
	nb_getval(claspver, V), V #>= 4,
	write_term(Min, [max_depth(0), numbervars(true)]),
	write('{'),
	plist2(BList),
	write('}'),
	write_term(Max, [max_depth(0), numbervars(true)])
	.
portray('#minimize' L) :-
	nb_getval(claspver, V), V #>= 4,
	write('#minimize {'),
	plist2(L),
	write('}')
	.


plist([]).
plist([E]) :-
	!,
	write(E)
	.
plist([E|L]) :-
	write(E),
	write(','),
	plist(L).

plist2([]).
plist2([E]) :-
	!,
	write(E)
	.
plist2([E|L]) :-
	write(E),
	write(';'),
	plist2(L).



%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%	test data can be used in the web demo. Actually, test_profile2
%	is used

test_profile(['test/ex12-1.pl','test/ex12-2.pl']).
test_profile2(['test/archeo1-1.pl','test/archeo1-2.pl','test/archeo1-3.pl','test/archeo1-ic.pl']).





test12 :-
	test_profile(Prof),
	test_rsf(Prof,sigma,strong,rsets).

























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

    This module implements predicates which runs an ASP solver on some
    program. It also declares necessary operators for ASP programs
    generation.
*/

:-module(asp,[
	      run/2,
	      run/3,

	      op(900,fy,not),
	      op(900,fy,'#minimize'),
	      op(900,fy,'#domain'),
	      op(900,fy,'#hide'),
	      op(700,xfy,'..'),
	      op(700,xfx,'!=')
	     ]).

:-use_module(utils,[chars_codes/2]).

:-use_module(library(process)).
:-use_module(library(readutil)).
:-use_module(library(charsio)).
:-use_module(library(clpfd)).



%%	run(+File,-Results)
%
%	Runs an asp solver on the specified File and collect
%	Results. At this time, the only supportedd solver is solver is
%	clingo.

run(File,Results) :-
	run(File,Results,[opt(none)])
	.

%%	run(+File,-Results,+Options)
%
%	Runs an asp solver on the specified File and collect
%	Results. At this time, the only supportedd solver is solver is
%	clingo. Option is a list of options. Actually, the supported
%	options are :
%	- opt(none) synonym for no option
%	- opt(inclmin) keep removed sets which are minimal with respect
%	  to set inclusion. Beware, this is performed by a
%	  post-processing, i.e. all removed sets are computed, and then
%	  the minimal ones are filtered.
%	- opt(prog) : keep the removed sets computed by the optimization
%	  implemented inthe program.

run(File,Results,[]) :-
	run(File,Results,[opt(none)]).
run(File,Results,[Opt]) :-
	nb_getval(clasppath, Path),
	% --opt-mode=optN is the new syntax of --opt-all (clingo 4.4.0)
	nb_getval(claspver, V),
	(   V #= 3
	->  OPTOPT = '--opt-all'
	;   OPTOPT = '--opt-mode=optN'
	),
	process_create(Path, [0, OPTOPT,File], [stdout(pipe(PH)),detached(true)]),
	collect_results(PH,Results1),
	close(PH,[force(true)]), % hack
	post_process(Results1,Results,Opt)
	.

%%	post_process(+InResults, -OutResults, +Option)
%
%	Do some post processing on collected results.
%	Option is a opt/1 term with the following significance :
%	none : no optimization : collect all answer sets (i.e. all
%	       potiential removed sets).
%	inclmin : keep inclusion-minimal potential remove sets.
%	prog : keep removed sets given by the optimization implemented
%	       in the program.
%	TODO : séparer (et autoriser) trois cas :
%	- inclmin seul : comme avant : on garde les incl-min de tous les
%	  answer sets.
%	- prog seul : comme avant : on garde les answer sets optimisés
%	  du prog.
%	- prog+inclmin : on garde les answer sets optimisés, et parmi
%	  ceux-ci on garde les minimaux suivants l'inclusion.

post_process(InResults, OutResults,opt(none)) :-
	filter_nonopt_results(InResults,OutResults)
	.
post_process(InResults, OutResults,opt(inclmin)) :-
	filter_nonopt_results(InResults,R1),
	keep_inclmin(R1,OutResults)
	.
post_process(InResults, OutResults,opt(prog)) :-
	filter_results(InResults,R1),
	keep_min_opt(R1,[],R2),
	final_list(R2,OutResults)
	.

%%	collect_results(+Stream, -Results)
%
%	Reads, analyzes and collect results from clasp solver.

collect_results(Stream,Results) :-
	read_line_to_codes(Stream,Line),
	chars_codes(LineC,Line),
	(   Line = end_of_file ->
	    Results = [];
	    % ->
	    parse_result_line(LineC,R),
	    (	R = end ->
	        Results = [];
	        % true
	        (   R = garbage ->
		    collect_results(Stream, Results);
		    % true
	            Results = [R|Results1],
	            collect_results(Stream,Results1)
		)
	    )
	)
	.

%%	filter_nonopt_results(+In,-Out)
%
%	Removes garbage from ASP solver output, i.e. keep only answer
%	sets lines.
%
%       !! CUT !!

filter_nonopt_results([],[]) :- !.
filter_nonopt_results([as(AS)|L1],[AS|L2]) :-
	!,
	filter_nonopt_results(L1,L2).
filter_nonopt_results([_|L1],L2) :-
	filter_nonopt_results(L1,L2)
	.

%%	filter_results(+In, -Out)
%
%	Removes garbage, writes triples (Answer #, optimisation value,
%	answer set) in a compact way.
%
%	!! CUT !!

filter_results([],[]) :- !.
filter_results([garbage|L1],L2) :- !,
	filter_results(L1,L2)
	.
filter_results([answer_num(N),as(AS),optimization(O)|L1],[N/O/AS|L2]) :-
	filter_results(L1,L2)
	.

%%	keep_inclmin(+Collection,?MinIncl)
%
%	Succeeds if MinIncl is the collection of inclusion-minimal
%	sets of Collection.

keep_inclmin(Collection,MinIncl) :-
	keep_inclmin([],[],Collection,MinIncl)
	.
%%	keep_inclmin(+Choosen,+Rejected,+Collection,?Result)
%
%	Upon success, Result contains the sets from Collection
%	which are minimal according to set inclusion in Collection U
%	Rejected, plus the sets which are initially in Chosen. The set
%	inclusion test is performed on rsf/2 atoms only.
%	See keep_inclmin/2 for everyday use !

keep_inclmin(S,_,[],S) :- !.
keep_inclmin(InS,R,[AS|L],OutS) :-
	append([InS,R,L],Compare),
	is_incl_min(AS,Compare), !,
	keep_inclmin([AS|InS],R,L,OutS)
	.
keep_inclmin(InS,R,[AS|L],OutS) :-
	keep_inclmin(InS,[AS|R],L,OutS)
	.

%%	is_incl_min(+Set, +Collection)
%
%	Tests wether Set is minimal according to set inclusion in
%	Collection. The set inclusion test is erformed on rsf/2 atoms
%	only.

is_incl_min(_,[]).
is_incl_min(S,[S1|L]) :-
	\+ rsubset(S1,S),
	is_incl_min(S,L)
	.
is_incl_min(S,[S1|L]) :-
	rsubset(S1,S),
	rsubset(S,S1),
	is_incl_min(S,L)
	.


%%	rsubset(?S1,?S2)
%
%	True if all rsf/2 atoms in S1 are also in S2.

rsubset([],_).
rsubset([rsf(X,Y)|L],S2) :-
	member(rsf(X,Y),S2),
	rsubset(L,S2)
	.
rsubset([A|L],S2) :-
	A \= rsf(_,_),
	rsubset(L,S2)
	.


%%	Keep minimize optimization results

keep_min_opt([],L,L).
keep_min_opt([N/O/AS|L],[],Final) :-
	keep_min_opt(L,[N/O/AS],Final)
	.
keep_min_opt([N/O/AS|L],[_/O1/_|_],Final) :-
	O #< O1,
	keep_min_opt(L,[N/O/AS],Final)
	.
keep_min_opt([N/O/AS|L],[N1/O1/AS1|L1],Final) :-
	O #= O1,
	keep_min_opt(L,[N/O/AS,N1/O1/AS1|L1],Final)
	.
keep_min_opt([_/O/_|L],[N1/O1/AS1|L1],Final) :-
	O #> O1,
	keep_min_opt(L,[N1/O1/AS1|L1],Final)
	.

%%	Remove AS number and optimization info.

final_list([],[]).
final_list([_/_/AS|L1],[AS|L2]) :-
	final_list(L1,L2)
	.


%%	Answer set solver results parser.

parse_result_line(Line,R) :-
	phrase(result_line(R),Line,_)
	.

result_line(garbage) -->
	['c','l','i','n','g','o'], space ,['v','e','r','s','i','o','n'], space,
	versionspec(_)
	.
result_line(garbage) -->
	['R','e','a','d','i','n','g'], space, ['f','r','o','m'], space,
	dirspec(_)
	.
result_line(garbage) -->
	['S','o','l','v','i','n','g','.','.','.']
	.
result_line(answer_num(Num)) -->
	answernum(Num)
	.
result_line(optimization(Num)) -->
	optimize(Num)
	.
result_line(end) -->
	['O','P','T','I','M','U','M',' ','F','O','U','N','D']
	.
result_line(end) -->
	['S','A','T','I','S','F','I','A','B','L','E']
	.
result_line(as(AS)) -->
	answer_set(AS)
	.

%%	version specification (unused for now)

versionspec([V|VS]) -->
	number(V),
	subversion(VS).

subversion([V|VS]) -->
	['.'],
	number(V),
	subversion(VS)
	.
subversion([]) -->
	[]
	.

dirspec([C|DS]) -->
	[C],
	{\+ char_type(C, space)},
	dirspec(DS)
	.
dirspec([]) -->
	[]
	.

%%	Interpret the "Answer:" lines of clingo output.
answernum(Num) -->
	['A','n','s','w','e','r',':'], space, number(Num)
	.

%%	Interpret the "Optimization" lines of clingo output.
optimize(Num) -->
	['O','p','t','i','m','i','z','a','t','i','o','n',':'], space, number(Num)
	.

%%	collect answer sets from clingo output
answer_set([T|L]) -->
	term(LT),
	{
	 LT \= [],
	 chars_to_term(LT,T)
	},
	end_answer_set(L)
	.

end_answer_set([T|L]) -->
	[' '],
	term(LT),
	{
	    LT \= [],
	    chars_to_term(LT, T)
	},
	end_answer_set(L)
	.
end_answer_set([]) -->
	[' ']
	.
end_answer_set([]) -->
	[]
	.

term([C|L]) -->
	[C],
	{\+ char_type(C,space)},
	term(L)
	.
term([]) -->
	[]
	.


space -->
	[' '], space
	.
space -->
	[]
	.

number(N) -->
	digit(D0),
	digits(D),
	{ number_chars(N, [D0|D]) }
	.

digits([D|T]) -->
	digit(D),
	digits(T).
digits([]) --> [].

digit(D) -->
	[D],
	{ char_type(D,digit) }
	.



chars_to_term(Chars,Term) :-
	append(Chars,['.'],Chars1),
	open_chars_stream(Chars1,S),
	read(S,Term),
	close(S)
	.















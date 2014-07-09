%% -*- prolog -*-
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
%% License along with PLRsf-solver. If not, see
%% <http://www.gnu.org/licenses/>.
%%
%% PLRsf-Solver implements removed set fusion of logic programs.
%%
%% This files implements a demo web service for PLRSF.
%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-use_module(library(debug)).

:-use_module(library(clpfd)).

:- use_module(library(http/thread_httpd)).
:- use_module(library(http/http_dispatch)).
:- use_module(library(http/html_write)).
:- use_module(library(http/http_parameters)).
:- use_module(library(http/html_head)).
:- use_module(library(http/http_mime_plugin)).
:- use_module(library(http/http_client)).
:- use_module(library(http/http_path)).
:- use_module(library(uri)).

:- ensure_loaded('fusion.pl').
:- use_module(profileio).
:- use_module(logic).

:- http_handler(root(.), home, []).
:- http_handler(root(run), run, []).
:- http_handler(root(help), helppage, []).
:- http_handler(root(kbinput), kbinput, []).
:- http_handler(root(runsolver), runsolver, []).
:- http_handler(css('demo_rsf.css'), http_reply_file(css_files('demo_rsf.css'), []), []).


http:location(root, '/plrsfdemo', []).
http:location(css, root(css), []).

:- multifile user:file_search_path/2.

%%	change this during installation of the demo:

user:file_search_path(document_root,	'/home/wurbel/src/prolog/plrsf').
user:file_search_path(css_files,	document_root(css)).

%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	Global parameters.
%%
%%	Please be extremely careful with these. Remember that we deal
%%	with high complexity algorithms.
%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%	Maximum number of formulae in each belief base.

max_formulae(50).

%%	Maximum number of bases.

max_bases(5).

%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	HTTP requests handling.
%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%	server(+Port)
%%	Start the server on the given port.

server(Port) :-
        http_server(http_dispatch, [port(Port)]).


%%	home(+Request)
%	Provides the initial page.

home(_Request) :-
	reply_html_page(title('PLRSF demonstrator - Welcome'),
			[
			 \banner,
			 \menu_bar,
			 div(class(conteneur),
			     [
			      div(class(contenu),
				  [
				   h2('Welcome !'),
				   p(['Welcome to the PLRSF demonstrator. ',
				      'This demonstrator allows you to experiment ',
				      'with removed set fusion of logic programs, which implements merging ',
				      'operators over logic programs.'
				      ]),
				   p(['to run the demonstrator, choose ',
				      '"run" in the menu above. To get some help, '
				     ,'choose "help".'])
				   ])
			     ]),
			 \footer
			])
	.

%%	helppage(+Request)
%%	Serves the help page.

helppage(_Request) :-
	reply_html_page(title('PLRSF demonstrator - Help'),
			[
			 \banner,
			 \menu_bar,
			 div(class(conteneur),
			     [
			      div(class(contenu),
				  [
				   h2('Help'),
				   p(['Welcome to the PLRSF demonstrator. ',
				      'This demonstrator allows you to experiment ',
				      'with removed set fusion operators ',
				      'of profiles of logic programs.'
				      ]),
				   p(['PLRSF is fully described in [',a([href('#bib1'),id(nh1)],'1'), ',', a([href('#bib2'),id(nh2)],'2'),'].',
				      'It is a syntactic merging approach, which implements several merging strategies, namely:']),
				   ul([
				       li([strong('Sigma: '), 'the operator minimizes the total number of rules which must be '
					  ,'dropped in order to restore consistency.'
					  ]),
				       li([strong('Card: '), 'this strategy is closely related to Sigma. However, it does not '
					  ,'take into account rules repetitions over the programs in the profile.'
					  ]),
				       li([strong('Max: '), 'this strategy minimizes the number of rules dropped from the program '
					  ,'where this number is maximal.'
					  ]),
				       li([strong('GMax: '), 'is a lexicographic refinement of Max.'])
				      ]),
				   p(['Each qstrategy can lead to two different operators :']),
				   ul([
				       li([strong('strong merging :'), 'the goal of the merging operation is to restore stable models, i.e. it guarantees that the resulting program has at least one stable model.']),
				       li([strong('weak merging :'), 'the goal of the merging operation is to restore HT-models, i.e. it guarantees that the resulting program has at least one HT-model.'])
				       ]),
				   h2('Input'),
				   p(['The PLRSF demonstrator takes as input a profile, i.e. a multiset of logic programs, '
				     ,'and an optionnal program which acts as a set of integrity constraints, i.e. rules which '
				     ,'must be consistent with the result.'
				     ]),
				   p(['If you do not fill the integrity constraints, the demonstrator considers that your integrity constraints '
				     ,'consists in an empty program.'
				     ]),
				   h2('Output'),
				   p(['The output consists in a flock, that is, an alternative between several programs '
				     ,'which are all admissible solutions to the merging problem, according to the choosen '
				     ,'strategy and mode. This is the default behavior.']),
				   p(['An alternative behaviour is to request the display of the so-called ',em('removed sets'),', that is,'
				     ,'the sets of formulae which are dropped from the union of the programs in the profile'
				     ]),
				   h2('Syntax'),
				   p(['Each rule must finish with a dot. Propositionnal atoms must begin with a lowerase letter '
				     ,'(indeed, they must obey to the prolog definition of an atom). Well formed formulae are of the form '
				     ,' c :- a0,...,an,not b0,...,not bm. c, a0,...,an,b0,...,bn are literals, i.e. atoms or their strong negation (-).'
				     ]),
				   p(['to run the demonstrator, choose ',
				      '"run" in the menu above.'
				     ]),
				   div(class(bib),
				       [h3('Bibliography'),
					p(['[',a([href('#nh1'),id(bib1)],1),'] ',strong('Extending belief base change to logic programs with ASP'), ', '
					  ,em('Julien HUE, Odile PAPINI, Éric WÜRBEL,')
					  ,'in : College Publications, Trends in Belief Revision and Argumentation Dynamics., Studies in Logic, '
					  ,'2013, december, Eduardo L. Fermé, Dov M. Gabbay and Guillermo R. Simari, eds.'
					  ]),
					p(['[',a([href('#nh2'),id(bib2)],2),'] '
					  , strong('Belief Bases Represented by Logic Programs')
					  , ', '
					  , em('Julien HUE, Odile PAPINI, Éric WÜRBEL,')
					  , 'European Conference on Symbolic and Quantitative Approaches to Reasonning under Uncertainty (ECSQARU), '
					  , '2009, Verona, Italy, pages 371-382.'
					  ])
				       ])

				   ])
			     ]),
			 \footer
			])
	.


%%	run(+Request)
%%	runs the demonstrator. This is the first page (number of bases
%	input).

run(_Request) :-
	reply_html_page(title('PLRSF demonstrator - Run'),
			[
			 \banner,
			 \menu_bar,
			 div(class(conteneur),
			     [
			      div(class(contenu),
				  [\base_nb_input])
			     ]),
			 \footer
			])
	.

%%	kbinput(+Request)
%%	input of bases and strategy. This pages receives the number of
%	bases as a parameter whose name is basenb.

kbinput(Request) :-
	max_bases(MaxB),
	catch(http_parameters(Request,[basenb(NBKB,[optional(false),integer,between(2,MaxB)])]),
	      _, throw(http_reply(bad_request(bad_kb_number)))),
	reply_html_page(title('PLRSF demonstrator - Run'),
			[
			 \banner,
			 \menu_bar,
			 div(class(conteneur),
			     [
			      div(class(contenu),
				  [
				   \profile_input(NBKB)
				  ])
			     ]),
			 \footer
			])
	.

%%	runsolver(+Request)
%%	Runs the solver with the received parameters (POST method). Thee
%	parameters are : the belief bases, the constraints, the merging
%	strategy and an putput option.

runsolver(Request) :-
	(   memberchk(method(post),Request),
	    http_read_data(Request, Parts, [form_data(mime)])
	->  % process parameters
	    get_mode(Parts,M),
	    get_strategy(Parts,S),
	    get_result_option(Parts,R),
	    get_profile(Parts,P),
	    run_rsf(S,M,R,P,Result),
	    reply_html_page(title('PLRSF demonstrator - Results'),
			    [
			     \banner,
			     \menu_bar,
			     div(class(conteneur),
				 [
				  div(class(contenu),
				      [
				       \display_results(S,M,R,P,Result)
				      ])
				 ]),
			     \footer
			    ])
	;    throw(http_reply(bad_request(bad_format)))
	)
	.

%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	Auxiliary predicates
%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%	get_mode(+Parts,-Mode)
%%	Reads the merging mode in the mime/multipart data

get_mode(Parts,Data) :-
	member(mime(Attributes, Data, []), Parts),
	memberchk(name(mode),Attributes),
	(   memberchk(Data,[weak,strong])
	->  true
	;   throw(http_reply(bad_request(bad_mode)))
	)
	.


%%	get_strategy(+Parts,-Strategy)
%%	Reads the strategy in the mime/multipart data

get_strategy(Parts,Data) :-
	member(mime(Attributes, Data, []), Parts),
	memberchk(name(strategy),Attributes),
	(   memberchk(Data,[sigma,card,max,gmax,inclmin,all])
	->  true
	;   throw(http_reply(bad_request(bad_strategy)))
	)
	.

%%	get_result_option(+Parts,-Opt)
%%	Reads the result output option in the mime/multipart data

get_result_option(Parts,Data) :-
	member(mime(Attributes, Data, []), Parts),
	memberchk(name(result),Attributes),
	(   memberchk(Data,[all,rsets])
	->  true
	;   throw(http_reply(bad_request(bad_output_option)))
	)
	.

%%	get_profile(+Parts,-Profile)
%%	Reads the belief profile in the mime/multipart data

get_profile(Parts,P) :-
	get_profile(1,Parts,P),
	check_nb_form(P)
	.

get_profile(N,Parts,[Name-Wff|P]) :-
	atomic_concat(base,N,Name),
	member(mime(Attributes, Data, []), Parts),
	memberchk(name(Name),Attributes),
	!,
	atom_codes(Data,Str),
	open_chars_stream(Str,Stream),
	catch(read_wff_loop(Stream,_,Wff),
	      logic_error(_,_),
	      throw(http_reply(bad_request(bad_formula)))),
	close(Stream),
	N1 #= N+1,
	get_profile(N1,Parts,P)
	.
get_profile(_N,Parts,Out) :-
	member(mime(Attributes, Data, []), Parts),
	memberchk(name(ic),Attributes),
	atom_codes(Data,Str),
	open_chars_stream(Str,Stream),
	catch(read_wff_loop(Stream,_,Wff),
	      logic_error(_,_),
	      throw(http_reply(bad_request(bad_formula)))),
	close(Stream),
	(   Wff = true
	->  Out = []
	;   Out = [ic-Wff]
	)
	.

%%	check_nb_form(+Profile)
%%	Check the number of formulae in each base. The limit is given by
%	max_formulae/1.

check_nb_form([]) :- !.
check_nb_form([_Name-Forms|P]) :-
	conjunct_size(Forms, N),
	max_formulae(Max),
	N =< Max,
	!,
	check_nb_form(P)
	.
check_nb_form(_) :-
	throw(http_reply(bad_request(too_much_formulae)))
	.



%%	strat_labal(?Strat, ?Label)
%%	Correspondence between a strategy and its associated label.

strat_label(sigma,	'Sigma').
strat_label(card,	'Card').
strat_label(max,	'Max').
strat_label(gmax,	'GMax').
strat_label(inclmin,	'Inclusion minimal').
strat_label(all,	'All potential removed sets').

%%	output_opt_label(?Opt, ?Label)
%%	Correspondence between an output option and its asociated label.
%

output_opt_label(all, 'All belief bases').
output_opt_label(rsets, 'Removed sets').

%%	mode_label(?Mode, ?Label)
%%	Correspondence between a merging mode and its associated lebal.

mode_label(weak,	'Weak').
mode_label(strong,	'Strong').

%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	Page generation rules.
%%
%%	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%	Serves a display of rsf results

display_results(Strat,Mode,ResOpt,Profile,Results) -->
	html([h2('Initial Profile:'),
	      \output_profile(Profile),
	      h2('Merging options:'),
	      \output_options(Strat,Mode,ResOpt),
	      h2('Merging result:'),
	      \output_results(Results,ResOpt,1)
	     ])
	.

%%	Serves a display of the initial profile

output_profile([]) --> [].
output_profile([ic-[]|Prof]) -->
	html([h3('No Integrity Constraints')]),
	output_profile(Prof)
	.
output_profile([ic-KB|Prof]) -->
	{
	 KB \= []
	},
	html([h3('Integrity Constraints'),
	      p(['{',\output_base(KB),'}'])
	     ]),
	output_profile(Prof)
	.
output_profile([Name-KB|Prof]) -->
	{ atom_concat('Belief Base ',Name, Title) },
	html([h3(Title),
	      p(['{',\output_base(KB),'}'])
	     ]),
	output_profile(Prof)
	.

%%	Serves a display of a knowledge base

output_base(Rule) -->
	{
	 Rule \= (_,_),
	 with_output_to(atom(A),write_term(Rule,[module(asp)]))
	},
	html([A,'.'])
	.
output_base((Rule,Conj)) -->
	{
	  Conj = (_,_),
	  with_output_to(atom(A),write_term(Rule,[module(asp)]))
	},
	html([A,'. ']),
	output_base(Conj)
	.
output_base((Rule1,Rule2)) -->
	{
	  Rule2 \= (_,_),
	  with_output_to(atom(A),write_term(Rule1,[module(asp)])),
	  with_output_to(atom(B),write_term(Rule2,[module(asp)]))
	},
	html([A,'. ',B,'.'])
	.

%%	Serves a display of the choosen options

output_options(Strat, Mode, ResOpt) -->
	{
	   strat_label(Strat, Str),
	   mode_label(Mode, M),
	   output_opt_label(ResOpt, R)
	},
	html([p(['Strategy: ',Str]),
	      p(['Mode: ',M]),
	      p(['Output options: ', R])])
	.

%%	Serves the results of the merging operation.

output_results([],_,_) --> [].
output_results([R|Results], ResOpt, N) -->
	{
	 (   ResOpt == all
	 ->  atom_concat('KB',N,Str)
	 ;   atom_concat('R',N,Str)
	 ),
	 N1 #= N + 1
	},
	html([h3([Str, ':']),
	      p(['{',\output_base(R),'}'])
	     ]),
	output_results(Results,ResOpt,N1)
	.

%%	Serves a form allowing to input options. The three options are
%	the merging strategy, the operator mode (weak or strong) and
%	the output option.

rsf_options -->
	html([
	    p([label([for='mode'],'Merging mode'),
	       select([name(mode),id(mode)],
		      [
		       option([selected,value(strong)], 'Strong'),
		       option([value(weak)], 'Weak')
		      ])
	      ]),
	    p([label([for='strategy'],'Merging strategy'),
	       select([name(strategy),id(strategy)],
		      [
		       option([selected,value(sigma)], 'Sigma'),
		       option([value(card)], 'Card'),
		       option([value(max)], 'Max'),
		       option([value(gmax)], 'GMax'),
		       option([value(inclmin)], 'Incl-min '),
		       option([value(all)], 'All')
		      ])
	      ]),
	    p([label([for='result'],'Result type'),
	       select([name(result),id(result)],
		      [
		       option([selected,value(all)], 'All belief bases'),
		       option([value(rsets)], 'Removed sets')
		      ])
	      ])
	     ])
	.

%%	Serves a form allowing to input the belief bases in the profile.

profile_input(NBKB) -->
	{ http_link_to_id(runsolver,[],Ref) },
	html([div(classform,
		  [form([id(kbinput),
			 action(Ref),
			 method('POST'),
			 enctype('multipart/form-data')
			],
			[
			 \rsf_options,
			 \kb_input(NBKB),
			 p(input([type(submit),value('Go')]))
			])
		  ])
	     ])
	.

%%	Serves a control allowing to input a belief base.

kb_input(0) -->
	html([p(label(for(ic),'Integrity Constraints (optional)')),
	      p(textarea([id(ic),name(ic),rows(10),cols(80)],[]))])
	.
kb_input(N) -->
	{
	  N > 0,
	  atomic_concat(base,N,Name),
	  atomic_concat('Belief Base ',N,LabelText)
	},
	{ N1 #= N - 1 },
	kb_input(N1),
	html([p(label(for(Name),LabelText)),
	      p(textarea([id(Name),name(Name),rows(10),cols(80)],[]))])
	.


%%	Serves a form allowing to input the number of belief bases in
%	the profile.

base_nb_input -->
	{ http_link_to_id(kbinput,[],Ref) },
	html(div(class=form,
		 [form([id(kbnbinput),action(Ref)],
		       [
			label(for(nbases),'Number of bases in the profile: '),
			input([type(text),name(basenb),id(nbases),size(2)]),
			input([type(submit),value('Next')])
		       ])
		 ]))
	.


%%	Serves the banner.

banner -->
	html([\html_requires(css('demo_rsf.css')),
	      div(class(banner),
		  h1('PLRSF Demonstrator'))
	     ])
	.

%%	Serves the menu of the demonstrator.

menu_bar -->
	{
	  http_link_to_id(home,[],HREF_HOME),
	  http_link_to_id(run,[],HREF_RUN),
	  http_link_to_id(helppage,[],HREF_HELP)
	},
	html(div(class(menu),
		 [ul([
		     li(a(href(HREF_HOME),'Home')),
		     li(a(href(HREF_RUN),'Run')),
		     li(a(href(HREF_HELP),'Help'))
		    ]),
		  div(class(nettoyeur),[])
		 ]))
	.

%%	Serves the footer.

footer -->
	html(div(class(footer),
		 p('Copyright 2012-2014 Éric Würbel LSIS CNRS UMR7296, Université de Toulon')))
	.

%%	Body common stuff.

body(Content) -->
	html(body([div(id(page),
		       Content)]))
	.

%%	Exception handling.
%
:- multifile prolog:message//1.

%%	These are the message to use for test phase. Do NOT use these
%	messages in a production environment, because they are too
%	informative, so they can guide a malicious software in an
%	attempt to break the security of the server.
%	See below for the production messages.

prolog:message(bad_kb_number) -->
        [ 'the number of belief bases is badly specified', nl,
          '(should be between 2 and 4)'
        ].
prolog:message(bad_format) -->
        [ 'badly formed request'
        ].
prolog:message(bad_formula) -->
        [ 'bad formula'
        ].
prolog:message(bad_strategy) -->
        [ 'bad strategy'
        ].
prolog:message(bad_mode) -->
        [ 'bad mode'
        ].
prolog:message(bad_output_option) -->
        [ 'bad output option'
        ].
prolog:message(too_much_formulae) -->
        [ 'too much formulae'
        ].


%%	Enable these messages when switching to production phase.

%prolog:message(bad_kb_number) -->
%        [ 'bad data'
%        ].
%prolog:message(bad_format) -->
%        [ 'badly formed request'
%        ].
%prolog:message(bad_formula) -->
%        [ 'bad data'
%        ].
%prolog:message(bad_strategy) -->
%        [ 'bad data'
%        ].
%prolog:message(bad_mode) -->
%        [ 'bad data'
%        ].
%prolog:message(bad_output_option) -->
%        [ 'bad data'
%        ].
%prolog:message(too_much_formulae) -->
%        [ 'bad data'
%        ].














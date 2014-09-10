%% -*- prolog -*-
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Copyright 2012_2014 Éric Würbel, LSIS-CNRS, Université de Toulon
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
%% This file is the initialization file of the PLRSF webdemo.
%%
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- ensure_loaded('webdemo.pl').

run :-
	html_set_options([dialect(xhtml)]),
	server(5000),
	thread_get_message(stop).

:- on_signal(hup, _, hup).

hup(_Signal) :-
        thread_send_message(main, stop).

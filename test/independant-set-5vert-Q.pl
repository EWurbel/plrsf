% find maximal independant sets usig a revision process.  This set Q
% represents the graph and the conditions for a candidate set of
% vertices to be an independant set.
%
% This example is questionnable as a revision example, but it
% illustrates the transformation used for the complexity
% DP-completeness proof.
kbname(ic).

e(1,2).
e(2,3).
e(3,1).
e(3,4).
e(4,5).
e(5,3).

isp(1) :- not is(1).
isp(2) :- not is(2).
isp(3) :- not is(3).
isp(4) :- not is(4).
isp(5) :- not is(5).

:- isp(1), isp(2), isp(3), isp(4), isp(5).

:- is(1), is(2), e(1,2).
:- is(2), is(3), e(2,3).
:- is(3), is(1), e(3,1).
:- is(3), is(4), e(3,4).
:- is(4), is(5), e(4,5).
:- is(5), is(3), e(5,3).


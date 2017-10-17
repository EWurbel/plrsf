plrsf V1.0.3
============

(c) 2012-2017 Éric Würbel, LSIS-CNRS UMR7196
<eric.wurbel@lsis.org>

plrsf is an application which implements Removed Set Merging of logic
programs with answer set semantics [1,2].

Removed set merging of logic programs consists in the retraction of
rules from logic programs in order to restore consistency.

Two flavours of consistency of logic programs are considered : in a
first definition, a program is considered as consistent iff it has at
least one answer set. In a second definition, a program is considered
consistent iff it has at least one SE-model.

The problem addressed by plrsf is as follows : considering a profile
{P1,...,Pn} of logic programs (i.e. a multi-ensemble of logic
programs), perform the merging of these programs. If the union of the
programs is consistent, then the merging is a simple union, otherwise
plrsf removes some rules from som profiles according to different
strategies in order to restore consistency.

See the documentation in =doc= folder for further instructions.

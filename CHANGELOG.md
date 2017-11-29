2017-11-29  Eric Würbel  <eric.wurbel@lsis.org>

	* generator.pl:

	- added term handling for atoms.

	- corrected a bug : in strong mode, exclusion between atoms and
	their auth/1 counterpart shoud only be performed on KB atoms,
	excluding IC atoms.

2017-10-16  Eric Würbel <eric.wurbel@lsis.org>

	* asp.pl

	- bumped licence dates

	* doc/plrsf-manual.tex:

	- adding an example in the documentation

	* fusion.pl

	- bumped licence dates

	* generator.pl

	- bumped licence dates

	* loader.pl

	- bumped licence dates

	* logic.pl

	- bumped licence dates

	* profileio.pl

	- bumped licence dates

	* strategy.pl

	- bumped licence dates

	* swiprolog.pl

	- bumped licence dates

	* utils.pl

	- bumped licence dates

	* webdemo.pl

	- bumped licence dates

	* webstarter.pl

	- bumped licence dates

2015-01-20  Eric Würbel <eric.wurbel@lsis.org>

	* fusion.pl

	- adding error:has_type(term) clauses. The reason is that the
	'term' type used in the library optparse is no longer working,
	because 'term' is not recognized by the error:has_type/2
	predicate. The most probable cause of this bug is a change in the
	error module.


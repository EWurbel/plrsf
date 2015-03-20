#! /bin/bash
# builing script for plrsf.

function usage() {
	echo "syntax : $0 [-e]" >&2
	echo >&2
	echo "Builds a standalone executable for plrsf and plrsf webdemo."  >&2
	echo >&2
	echo "options:" >&2
	echo "-e\tSpecifies that external libs should be embeded in the executable" >&2
}	


ext=false
while getopts "e" o; do
    case "$o" in
	e)   ext=true;;
	[?]) usage; exit 1;;
    esac
done

opts=""
if [ "$ext" = "true" ] ; then
    opts="--foreign=save"
fi

swipl $opts --stand_alone=true --goal="go,halt" --toplevel="halt(1)" -o plrsf -c loader.pl
swipl $opts --stand_alone=true --goal="true" --toplevel="run" -o plrsf-webdemo -c webstarter.pl
echo "==========================================================================="
echo "Compilation finished."
echo "The command line executable is available in the plrsf file."
echo "The web demo executable is available in the plrsf-webdemo file."
echo "==========================================================================="


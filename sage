#!/usr/bin/env bash

# WARNING: this function is copy/pasted from both src/bin/sage-env and
# the top-level "sage" script. Please keep them synchronized.
resolvelinks() {
    # $in is what still needs to be converted (normally has no starting slash)
    in="$1"
    # $out is the part which is converted (normally ends with trailing slash)
    out="./"

    # Move stuff from $in to $out
    while [ -n "$in" ]; do
        # Normalize $in by replacing consecutive slashes by one slash
        in=$(echo "${in}" | sed 's://*:/:g')

        # If $in starts with a slash, remove it and set $out to the root
        in_without_slash=${in#/}
        if [ "$in" != "$in_without_slash" ]; then
            in=$in_without_slash
            out="/"
            continue
        fi

        # Check that the directory $out exists by trying to cd to it.
        # If this fails, then cd will show an error message (unlike
        # test -d "$out"), so no need to be more verbose.
        ( cd "$out" ) || return $?


        # Get the first component of $in
        f=${in%%/*}

        # If it is not a symbolic link, simply move it to $out
        if [ ! -L "$out$f" ]; then
            in=${in#"$f"}
            out="$out$f"

            # If the new $in starts with a slash, move it to $out
            in_without_slash=${in#/}
            if [ "$in" != "$in_without_slash" ]; then
                in=$in_without_slash
                out="$out/"
            fi
            continue
        fi

        # Now resolve the symbolic link "$f"
        f_resolved=`readlink -n "$out$f" 2>/dev/null`
        status=$?
        # status 127 means readlink could not be found.
        if [ $status -eq 127 ]; then
            # We don't have "readlink", try a stupid "ls" hack instead.
            # This will fail if we have filenames like "a -> b".
            fls=`ls -l "$out$f" 2>/dev/null`
            status=$?
            f_resolved=${fls##*-> }

            # If $fls equals $f_resolved, then certainly
            # something is wrong
            if [ $status -eq 0 -a "$fls" = "$f_resolved" ]; then
                echo >&2 "Cannot parse output from ls -l '$out$f'"
                return 1
            fi
        fi
        if [ $status -ne 0 ]; then
            echo >&2 "Cannot read symbolic link '$out$f'"
            return $status
        fi

        # In $in, replace $f by $f_resolved (leave $out alone)
        in="${in#${f}}"
        in="${f_resolved}${in}"
    done

    # Return $out
    echo "$out"
}

# Resolve the links in $0 so that local/bin/sage can be executed from
# a symlink (Trac #30888).
SELF=$(resolvelinks "${0}")

# Display the current version of Sage
# usage: sage_version [-v]
#   -v    display the full version banner including release date
sage_version() {
    if [ -f "${SELF}-version.sh" ]; then
        . "${SELF}-version.sh"
    else
        . "$SAGE_ROOT/src/bin/sage-version.sh"
    fi

    if [ "$1" = "-v" ]; then
        echo "${SAGE_VERSION_BANNER}"
    else
        echo "${SAGE_VERSION}"
    fi
}

usage() {
    sage_version -v
    ####  1.......................26..................................................78
    ####  |.....................--.|...................................................|
    echo
    echo "Optional arguments:"
    echo "  file.[sage|py|spyx] -- run given .sage, .py or .spyx file"
    echo "  --advanced          -- list all command line options"
    echo "  -c <cmd>            -- Evaluates cmd as sage code"
    echo "  --gap [...]         -- run Sage's Gap with given arguments"
    echo "  --gp [...]          -- run Sage's PARI/GP calculator with given arguments"
    echo "  -h                  -- print this help message"
    echo "  --pip [...]         -- invoke pip, the Python package manager"
    echo "  --maxima [...]      -- run Sage's Maxima with given arguments"
    echo "  --mwrank [...]      -- run Sage's mwrank with given arguments"
    echo "  --notebook=[...]    -- start the Sage notebook (valid options are"
    echo "                         'default', 'jupyter', 'jupyterlab', and 'export')"
    echo "                         Current default is 'jupyter'"
    echo "  -n, --notebook      -- shortcut for --notebook=default"
    echo "  --python [...], --python3 [...] -- run the Python 3 interpreter"
    echo "  -R [...]            -- run Sage's R with given arguments"
    echo "  --singular [...]    -- run Sage's singular with given arguments"
    echo "  --nodotsage         -- run Sage without using the user's .sage directory:"
    echo "                         create and use a temporary .sage directory instead"
    echo "  -t [options] <--all|files|dir>"
    echo "                      -- test examples in .py, .pyx, .sage, .tex or .rst files"
    echo "                         selected options:"
    echo "                           --long - include lines with the phrase 'long time'"
    echo "                           --verbose - print debugging output during the test"
    echo "                           --optional - controls which optional tests are run"
    echo "                           --help - show all testing options"
    echo "  -v, --version       -- display Sage version information"
    if [ -n "$SAGE_ROOT" ]; then
        exec "$SAGE_ROOT/build/bin/sage-site" "-h"
    fi
    exit 0
}

# 'usage_advanced', which prints a longer help message, is defined
# below, after sourcing sage-env.

# Determine SAGE_ROOT, SAGE_LOCAL, and SAGE_VENV.
unset SAGE_VENV
if [ -x "${SELF}-config" ]; then
    # optional sage-config console script, installed by sage_conf
    export SAGE_ROOT=$("${SELF}-config" SAGE_ROOT)
    export SAGE_LOCAL=$("${SELF}-config" SAGE_LOCAL)
fi
if [ -f "${SELF}-src-env-config" ]; then
    # Not installed script, present only in src/bin/
    SAGE_SRC_ENV_CONFIG=1
    . "${SELF}-src-env-config" >&2
fi
if [ -z "$SAGE_VENV" -a -x "${SELF}-venv-config" ]; then
    # installed by setup.py
    export SAGE_VENV=$("${SELF}-venv-config" SAGE_VENV)
fi
if [ -f "${SELF}-env-config" ]; then
    # As of Trac #22731, sage-env-config is optional.
    . "${SELF}-env-config" >&2
fi

#####################################################################
# Special options to be processed without sage-env
#####################################################################

# Check for '--nodotsage' before sourcing sage-env; otherwise sage-env
# will already have set some environment variables with the old
# setting for DOT_SAGE.
if [ "$1" = '--nodotsage' ]; then
    export DOT_SAGE=`mktemp -d ${TMPDIR:-/tmp}/dotsageXXXXXX`
    shift
    command "${SELF}" "$@"
    status=$?
    rm -rf "$DOT_SAGE"
    exit $status
fi

# Check for '--patchbot' before sourcing sage-env: patchbot needs
# an unclobbered environment before testing unsafe tickets.
if [ "$1" = '-patchbot' -o "$1" = "--patchbot" ]; then
    shift
    # We ask the Python from Sage where the patchbot is installed.
    # We set PYTHONPATH to that directory such that the system Python
    # should also find the sage_patchbot package.
    cmd='import sage_patchbot as p; import os; print(os.path.dirname(p.__path__[0]))'
    export PYTHONPATH=`"$SAGE_ROOT/sage" --python3 -c "$cmd"`
    if [ -z "$PYTHONPATH" ]; then
        # Something went wrong, assume that the patchbot is not installed
        echo >&2 "Error: cannot find installation path for sage_patchbot"
        echo >&2 "See https://wiki.sagemath.org/buildbot for instructions"
        exit 1
    fi

    shopt -s execfail  # Do not exit if "exec" fails
    exec python3 -m sage_patchbot.patchbot "$@"
    echo >&2 "Error: cannot find a suitable Python 3 program."
    echo >&2 "The SageMath patchbot requires a system Python 3 installation."
    exit 127
fi

# Check for '-i' before sourcing sage-env: running "make"
# should be run outside of the Sage shell.
if [ "$1" = '-f' ]; then
    # -f is an alias for -i -f
    set -- -i "$@"
fi

if [ "$1" = '-i' ]; then
    shift
    if [ -z "$MAKE" ]; then
        MAKE="make"
    fi

    set -e
    cd "$SAGE_ROOT"

    # Parse options
    PACKAGES=""         # Packages to install
    INSTALL_OPTIONS=""  # Options to sage-spkg
    for OPT in "$@"; do
        case "$OPT" in
            -info|--info)
                echo >&2 "Error: 'sage -i $OPT <package>' is no longer supported, use 'sage --info <package>' instead."
                exit 2;;
            -f) FORCE_INSTALL=yes;;
            # Setting SAGE_CHECK here duplicates what we do in sage-spkg
            # but we need it in "make" already when there are (order-only)
            # dependencies on packages providing test infrastructure
            -c) INSTALL_OPTIONS="$INSTALL_OPTIONS $OPT"; export SAGE_CHECK=yes;;
            -w) INSTALL_OPTIONS="$INSTALL_OPTIONS $OPT"; export SAGE_CHECK=warn;;
            -*) INSTALL_OPTIONS="$INSTALL_OPTIONS $OPT";;
            *) PACKAGES="$PACKAGES $OPT";;
        esac
    done

    # First, uninstall the packages if -f was given
    if [ "$FORCE_INSTALL" = yes ]; then
        for PKG in $PACKAGES; do
            $MAKE "$PKG-clean" || true  # Ignore errors
        done
    fi

    # Make sure that the toolchain is up-to-date
    # (which is a dependency of every package)
    $MAKE all-toolchain

    ALL_TARGETS="$($MAKE list 2>/dev/null)"

    # Now install the packages
    for PKG in $PACKAGES; do
        echo
        # Check that $PKG is actually a Makefile target
        # See https://trac.sagemath.org/ticket/25078
        if ! echo "$ALL_TARGETS" | grep "^${PKG}$" >/dev/null; then
            echo >&2 "Error: package '$PKG' not found"
            echo >&2 "Note: if it is an old-style package, installing these is no longer supported"
            exit 1
        fi
        $MAKE SAGE_SPKG="sage-spkg $INSTALL_OPTIONS" "$PKG"
    done
    echo "New packages may have been installed."
    echo "Re-running configure and make in case any dependent packages need updating."
    touch "$SAGE_ROOT/configure" && $MAKE all-build
    exit 0
fi

#####################################################################
# Report information about the Sage environment
#####################################################################

if [ "$1" = '-dumpversion' -o "$1" = '--dumpversion' ]; then
        sage_version
        exit 0
fi

if [ "$1" = '-v' -o "$1" = '-version' -o "$1" = '--version' ]; then
        sage_version -v
        exit 0
fi

if [ "$1" = '-root'  -o "$1" = '--root' ]; then
    echo "$SAGE_ROOT"
    exit 0
fi


#####################################################################
# Source sage-env ($SELF is the name of this "sage" script, so we can just
# append -env to that). We redirect stdout to stderr, which is safer
# for scripts.
#####################################################################
if [ -f "${SELF}-env" ]; then
    . "${SELF}-env" >&2
    if [ $? -ne 0 ]; then
        echo >&2 "Error setting environment variables by sourcing '${SELF}-env';"
        echo >&2 "possibly contact sage-devel (see http://groups.google.com/group/sage-devel)."
        exit 1
    fi
fi

if [ -f "${SELF}-src-env-config.in" ]; then
    # The sage script is being run out of SAGE_ROOT/src/bin.
    # In this case, put this directory in the front of the PATH.
    export PATH="$SAGE_SRC/bin:$PATH"
fi

if [ -z "$DOT_SAGE" ]; then
    export DOT_SAGE="$HOME/.sage"
fi


#####################################################################
# Helper functions
#####################################################################

# Prepare for running Sage, either interactively or non-interactively.
sage_setup() {
    # Check that we're not in a source tarball which hasn't been built yet (#13561).
    if [ "$SAGE_SRC_ENV_CONFIG" = 1 ] && [ ! -z "$SAGE_VENV" ] && [ ! -x "$SAGE_VENV/bin/sage" ]; then
        echo >&2 '************************************************************************'
        echo >&2 'It seems that you are attempting to run Sage from an unpacked source'
        echo >&2 'tarball, but you have not compiled it yet (or maybe the build has not'
        echo >&2 'finished). You should run `make` in the Sage root directory first.'
        echo >&2 'If you did not intend to build Sage from source, you should download'
        echo >&2 'a binary tarball instead. Read README.txt for more information.'
        echo >&2 '************************************************************************'
        exit 1
    fi

    maybe_sage_location

    if [ ! -d "$IPYTHONDIR" ]; then
        # make sure that $DOT_SAGE exists so that ipython will happily
        # create its config directories there.  If DOT_SAGE doesn't
        # exist, ipython complains.
        mkdir -p -m 700 "$DOT_SAGE"
    fi
    sage-cleaner &>/dev/null &
}


# Check to see if the whole Sage install tree has moved.  If so,
# change various hardcoded paths.  Skip this if we don't have write
# access to $SAGE_LOCAL (e.g. when running as a different user) or
# if Python and sage-location haven't been installed yet.
maybe_sage_location()
{
    if [ -n "$SAGE_LOCAL" -a -w "$SAGE_LOCAL" ]; then
        if [ -x "$SAGE_VENV/bin/python" ] && [ -x "$SAGE_VENV/bin/sage-location" ]; then
            sage-location || exit $?
        fi
    fi
}


# Start an interactive Sage session, this function never returns.
interactive_sage() {
    sage_setup
    exec sage-ipython "$@" -i
}

#####################################################################
# sage --advanced
#####################################################################

usage_advanced() {
    sage_version -v
    ####  1.......................26..................................................78
    ####  |.....................--.|...................................................|
    echo
    echo "Running Sage, the most common options:"
    echo
    echo "  file.[sage|py|spyx] -- run given .sage, .py or .spyx file"
    echo "  -h, -?, --help      -- print a short help message"
    echo "  -v, --version       -- print the Sage version"
    echo "  --advanced          -- print this list of Sage options"
    echo "  -c cmd              -- evaluate cmd as sage code. For example,"
    echo "                         \"sage -c 'print(factor(35))'\" will"
    echo "                         print \"5 * 7\"."
    echo
    echo "Running Sage, other options:"
    echo
    echo "  --dumpversion       -- print brief Sage version"
    echo "  --preparse file.sage -- preparse \"file.sage\", and produce"
    echo "                          the corresponding Python file"
    echo "                          \"file.sage.py\""
    echo "  -q                  -- quiet; start with no banner"
    echo "  --min               -- do not populate global namespace"
    echo "                         (must be first option)"
    echo "  --nodotsage         -- run Sage without using the user's"
    echo "                         .sage directory: create and use a temporary"
    echo "                         .sage directory instead."
    echo "  --gthread, --qthread, --q4thread, --wthread, --pylab"
    echo "                      -- pass the option through to IPython"
    echo "  --simple-prompt     -- pass the option through to IPython: use"
    echo "                         this option with sage-shell mode in emacs"
    if [ -n "$SAGE_SRC" -a -d "$SAGE_SRC" ]; then
        echo "  --grep [options] <string>"
        echo "                      -- regular expression search through the Sage"
        echo "                         library for \"string\". Any options will"
        echo "                         get passed to the \"grep\" command."
        echo "  --grepdoc [options] <string>"
        echo "                      -- regular expression search through the"
        echo "                         Sage documentation for \"string\"."
        echo "  --search_src ...    -- same as --grep"
        echo "  --search_doc ...    -- same as --grepdoc"
    fi
    echo
    echo "Running external programs:"
    echo
    echo "  --cython [...]      -- run Cython with the given arguments"
    echo "  --ecl [...], --lisp [...]  -- run Sage's copy of ECL (Embeddable"
    echo "                                Common Lisp) with the given arguments"
    echo "  --gap [...]         -- run Sage's Gap with the given arguments"
    echo "  --gap3 [...]        -- run Sage's Gap3 with the given arguments"
    command -v gap3 &>/dev/null || \
    echo "                         (not installed currently, run sage -i gap3)"
    echo "  --gdb               -- run Sage under the control of gdb"
    echo "  --gdb-ipython       -- run Sage's IPython under the control of gdb"
    echo "  --git [...]         -- run Sage's Git with the given arguments"
    echo "  --gp [...]          -- run Sage's PARI/GP calculator with the"
    echo "                         given arguments"
    echo "  --ipython [...], --ipython3 [...]"
    echo "                      -- run Sage's IPython using the default"
    echo "                         environment (not Sage), passing additional"
    echo "                         additional options to IPython"
    echo "  --jupyter [...]     -- run Sage's Jupyter with given arguments"
    echo "  --kash [...]        -- run Sage's Kash with the given arguments"
    command -v kash &>/dev/null || \
    echo "                         (not installed currently, run sage -i kash)"
    echo "  --M2 [...]          -- run Sage's Macaulay2 with the given arguments"
    command -v M2 &>/dev/null || \
    echo "                         (not installed currently, run sage -i macaulay2)"
    echo "  --maxima [...]      -- run Sage's Maxima with the given arguments"
    echo "  --mwrank [...]      -- run Sage's mwrank with the given arguments"
    echo "  --pip [...]         -- invoke pip, the Python package manager"
    echo "  --polymake [...]    -- run Sage's Polymake with given arguments"
    command -v polymake &>/dev/null || \
    echo "                         (not installed currently, run sage -i polymake)"
    echo "  --python [...], --python3 [...]"
    echo "                      -- run the Python 3 interpreter"
    echo "  -R [...]            -- run Sage's R with the given arguments"
    echo "  --singular [...]    -- run Sage's singular with the given arguments"
    echo "  --sqlite3 [...]     -- run Sage's sqlite3 with given arguments"
    echo
    echo "Running the notebook:"
    echo
    echo "  -n [...], --notebook=[...]"
    echo "                      -- start the notebook; valid options include"
    echo "                         'default', 'jupyter', 'jupyterlab', and 'export'."
    echo "                         Current default is 'jupyter'."
    echo "                         Run \"sage --notebook --help\" for more details."
    echo
    ####  1.......................26..................................................78
    ####  |.....................--.|...................................................|
    echo "Testing files:"
    echo
    echo "  -t [options] <files|dir> -- test examples in .py, .pyx, .sage"
    echo "                              or .tex files.  Options:"
    echo "     --long           -- include lines with the phrase 'long time'"
    echo "     --verbose        -- print debugging output during the test"
    echo "     --all            -- test all files"
    echo "     --optional       -- also test all examples labeled \"# optional\""
    echo "     --only-optional[=tags]"
    echo "                      -- if no 'tags' are specified, only run"
    echo "                         blocks of tests containing a line labeled"
    echo "                         \"# optional\". If a comma-separated"
    echo "                         list of tags is specified, only run block"
    echo "                         containing a line labeled \"# optional tag\""
    echo "                         for any of the tags given, and in these blocks"
    echo "                         only run the lines which are unlabeled or"
    echo "                         labeled \"# optional\" or labeled"
    echo "                         \"# optional tag\" for any of the tags given."
    echo "     --randorder[=seed] -- randomize order of tests"
    echo "     --random-seed[=seed]  -- random seed (integer) for fuzzing doctests"
    echo "     --new            -- only test files modified since last commit"
    echo "     --initial        -- only show the first failure per block"
    echo "     --debug          -- drop into PDB after an unexpected error"
    echo "     --failed         -- only test files that failed last test"
    echo "     --warn-long [timeout] -- warning if doctest is slow"
    echo "     --only-errors    -- only output failures, not successes"
    echo "     --gc=GC          -- control garbarge collection (ALWAYS:"
    echo "                         collect garbage before every test; NEVER:"
    echo "                         disable gc; DEFAULT: Python default)"
    echo "     --short[=secs]   -- run as many doctests as possible in about 300"
    echo "                         seconds (or the number of seconds given.) This runs"
    echo "                         the tests for each module from the top of the file"
    echo "                         and skips tests once it exceeds the budget"
    echo "                         allocated for that file."
    echo "     --help           -- show all doctesting options"
    echo "  --tnew [...]        -- equivalent to -t --new"
    echo "  -tp <N> [...]       -- like -t above, but tests in parallel using"
    echo "                         N threads, with 0 interpreted as min(8, cpu_count())"
    echo "  --testall [options] -- equivalent to -t --all"
    echo
    echo "  --coverage <files>  -- give information about doctest coverage of files"
    echo "  --coverageall       -- give summary info about doctest coverage of"
    echo "                         all files in the Sage library"
    echo "  --startuptime [module] -- display how long each component of Sage takes to"
    echo "                         start up; optionally specify a module to get more"
    echo "                         details about that particular module"
    if [ -n "$SAGE_SRC" -a -f "$SAGE_SRC/tox.ini" ]; then
        echo "  --tox [options] <files|dirs> -- general entry point for testing"
        echo "                                  and linting of the Sage library"
        echo "     -e <envlist>     -- run specific test environments"
        echo "                         (default: run all except full pycodestyle)"
        tox -c "$SAGE_SRC" --listenvs-all -v 2>/dev/null | sed -n '/->/s/^/        /;s/(/\
                                  (/;s/->/   --/p;'
        echo "     -p auto          -- run test environments in parallel"
        echo "     --help           -- show tox help"
        command -v tox &>/dev/null || \
        echo "                         (not installed currently, run sage -i tox)"
    fi
    echo
    echo "Some developer utilities:"
    echo
    echo "  --sh [...]         -- run a shell with Sage environment variables"
    echo "                        as they are set in the runtime of Sage"
    echo "  --cleaner          -- run the Sage cleaner.  This cleans up after Sage,"
    echo "                        removing temporary directories and spawned processes."
    echo "                        (This gets run by Sage automatically, so it is usually"
    echo "                        not necessary to run it separately.)"
    ####  1.......................26..................................................78
    ####  |.....................--.|...................................................|
    echo "File conversion:"
    echo
    echo "  --rst2ipynb [...]   -- Generates Jupyter notebook (.ipynb) from standalone"
    echo "                         reStructuredText source."
    command -v rst2ipynb &>/dev/null || \
    echo "                         (not installed currently, run sage -i rst2ipynb)"
    echo "  --ipynb2rst [...]   -- Generates a reStructuredText source file from"
    echo "                         a Jupyter notebook (.ipynb)."
    echo "  --sws2rst <sws doc> -- Generates a reStructuredText source file from"
    echo "                         a Sage worksheet (.sws) document."
    command -v sage-sws2rst >&/dev/null || \
    echo "                         (not installed currently, run sage -i sage_sws2rst)"
    echo
    ####  1.......................26..................................................78
    ####  |.....................--.|...................................................|
    echo "Valgrind memory debugging:"
    echo
    echo "  --cachegrind        -- run Sage using Valgrind's cachegrind tool.  The log"
    echo "                         files are named sage-cachegrind.PID can be found in"
    echo "                         \$DOT_SAGE"
    echo "  --callgrind         -- run Sage using Valgrind's callgrind tool.  The log"
    echo "                         files are named sage-callgrind.PID can be found in"
    echo "                         \$DOT_SAGE"
    echo "  --massif            -- run Sage using Valgrind's massif tool.  The log"
    echo "                         files are named sage-massif.PID can be found in"
    echo "                         \$DOT_SAGE"
    echo "  --memcheck          -- run Sage using Valgrind's memcheck tool.  The log"
    echo "                         files are named sage-memcheck.PID can be found in"
    echo "                         \$DOT_SAGE"
    echo "  --omega             -- run Sage using Valgrind's omega tool.  The log"
    echo "                         files are named sage-omega.PID can be found in"
    echo "                         \$DOT_SAGE"
    echo "  --valgrind          -- this is an alias for --memcheck"
    if [ -n "$SAGE_ROOT" ]; then
        exec "$SAGE_ROOT/build/bin/sage-site" "--advanced"
    fi
    echo
    exit 0
}

if [ $# -gt 0 ]; then
  if [ "$1" = '-h' -o "$1" = '-?' -o "$1" = '-help' -o "$1" = '--help' ]; then
     usage
  fi
  if [ "$1" = "-advanced" -o "$1" = "--advanced" ]; then
     usage_advanced
  fi
fi


#####################################################################
# Running Sage
#####################################################################

if [ "$1" = '-min' -o "$1" = '--min' ]; then
    shift
    export SAGE_IMPORTALL=no
fi

if [ "$1" = '-q' ]; then
    shift
    export SAGE_BANNER=no
fi

if [ $# -eq 0 ]; then
    interactive_sage
fi

#####################################################################
# Other basic options
#####################################################################

if [ "$1" = '-c' ]; then
    shift
    sage_setup
    unset TERM  # See Trac #12263
    exec sage-eval "$@"
fi

if [ "$1" = '-preparse' -o "$1" = "--preparse" ]; then
    shift
    exec sage-preparse "$@"
fi

if [ "$1" = '-cleaner' -o "$1" = '--cleaner' ]; then
    exec sage-cleaner
fi

#####################################################################
# Run Sage's versions of Python, pip, IPython, Jupyter.
#####################################################################

if [ "$1" = '-pip' -o "$1" = '--pip' -o "$1" = "--pip3" ]; then
    shift
    exec python3 -m pip --disable-pip-version-check "$@"
fi

if [ "$1" = '-python' -o "$1" = '--python' -o  "$1" = '-python3' -o "$1" = '--python3' ]; then
    shift
    exec python3 "$@"
fi

if [ "$1" = '-ipython' -o "$1" = '--ipython' -o "$1" = '-ipython3' -o "$1" = '--ipython3' ]; then
    shift
    exec ipython3 "$@"
fi

if [ "$1" = '-jupyter' -o "$1" = '--jupyter' ]; then
    shift
    exec jupyter "$@"
fi

#####################################################################
# Run Sage's versions of its component packages
#####################################################################

if [ "$1" = "-cython" -o "$1" = '--cython' -o "$1" = '-pyrex' -o "$1" = "--pyrex" ]; then
    shift
    exec cython "$@"
fi

if [ "$1" = '-gap' -o "$1" = '--gap' ]; then
    shift
    exec gap "$@"
fi

if [ "$1" = '-gap3' -o "$1" = '--gap3' ]; then
    shift
    exec gap3 "$@"
fi

if [ "$1" = '-gp' -o "$1" = '--gp' ]; then
    shift
    exec gp "$@"
fi

if [ "$1" = '-polymake' -o "$1" = '--polymake' ]; then
    shift
    exec polymake "$@"
fi

if [ "$1" = '-singular' -o "$1" = '--singular' ]; then
    shift
    exec Singular "$@"
fi

if [ "$1" = '-sqlite3' -o "$1" = '--sqlite3' ]; then
    shift
    exec sqlite3 "$@"
fi

if [ "$1" = '-ecl' -o "$1" = '--ecl' ]; then
    shift
    exec ecl "$@"
fi

if [ "$1" = '-lisp' -o "$1" = '--lisp' ]; then
    shift
    exec ecl "$@"
fi

if [ "$1" = '-kash' -o "$1" = '--kash' ]; then
    shift
    exec kash "$@"
fi

if [ "$1" = '-maxima' -o "$1" = '--maxima' ]; then
    shift
    maxima_cmd=$(sage-config MAXIMA 2>/dev/null)
    if [ -z "${maxima_cmd}" ]; then
        maxima_cmd="maxima -l ecl"
    fi
    exec $maxima_cmd "$@"
fi

if [ "$1" = '-mwrank' -o "$1" = '--mwrank' ]; then
    shift
    exec mwrank "$@"
fi

if [ "$1" = '-M2' -o "$1" = '--M2' ]; then
    shift
    exec M2 "$@"
fi

if [ "$1" = '-R' -o "$1" = '--R' ]; then
    shift
    exec R "$@"
fi

if [ "$1" = '-git' -o "$1" = '--git' ]; then
    shift
    exec git "$@"
fi

#####################################################################
# sage --sh and sage --buildsh
#####################################################################

if [ "$1" = '-sh' -o "$1" = '--sh' -o "$1" = '-buildsh' -o "$1" = '--buildsh' ]; then
    # AUTHORS:
    # - Carl Witty and William Stein: initial version
    # - Craig Citro: add options for not loading profile
    # - Martin Albrecht: fix zshell prompt (#11866)
    # - John Palmieri: shorten the prompts, and don't print messages if
    #   there are more arguments to 'sage -sh' (#11790)
    if [ -z "$SAGE_SHPROMPT_PREFIX" ]; then
        SAGE_SHPROMPT_PREFIX=sage-sh
    fi
    if [ "$1" = '-buildsh' -o "$1" = '--buildsh' ]; then
        if [ ! -r "$SAGE_ROOT"/build/bin/sage-build-env-config ]; then
           echo "error: '$SAGE_ROOT' does not contain build/bin/sage-build-env-config.  Run configure first."
           exit 1
        fi
        . "$SAGE_ROOT"/build/bin/sage-build-env-config || (echo "error:  Error sourcing $SAGE_ROOT/build/bin/sage-build-env-config"; exit 1)
        . "$SAGE_ROOT"/build/bin/sage-build-env || (echo "error:  Error sourcing $SAGE_ROOT/build/bin/sage-build-env"; exit 1)
        export SAGE_SHPROMPT_PREFIX=sage-buildsh
        # We export it so that recursive invocation of 'sage-sh' from a sage-buildsh shows the sage-buildsh prompt;
        # this makes sense because all environment variables set in build/bin/sage-build-env-config
        # and build/bin/sage-build-env are exported.
    fi
    shift
    # If $SHELL is unset, default to bash
    if [ -z "$SHELL" ]; then
        export SHELL=bash
    fi
    # We must start a new shell with no .profile or .bashrc files
    # processed, so that we know our path is correct
    SHELL_NAME=`basename "$SHELL"`
    # Check for SAGE_SHPROMPT.  If defined, use for the prompt.  If
    # not, check for already-defined $PS1, and if defined use that.
    # $PS1 should only be available if it is defined in
    # $DOT_SAGE/sagerc.
    if [ -n "$SAGE_SHPROMPT" ]; then
        oldPS1=$SAGE_SHPROMPT
    elif [ -n "$PS1" ]; then
        oldPS1=$PS1
    fi
    # Set the default prompt.  If available, use reverse video to
    # highlight the string "(sage-sh)".
    if tput rev &>/dev/null; then
        color_prompt=yes
    fi
    case "$SHELL_NAME" in
        bash)
            SHELL_OPTS="--norc"
            if [ "$color_prompt" = yes ]; then
                PS1="\[$(tput rev)\]($SAGE_SHPROMPT_PREFIX)\[$(tput sgr0)\] \u@\h:\W\$ "
            else
                PS1="($SAGE_SHPROMPT_PREFIX) \u@\h:\w\$ "
            fi
            export PS1
            ;;
        csh)
            # csh doesn't seem to allow the specification of a different
            # .cshrc file, and the prompt can only be set in this file, so
            # don't bother changing the prompt.
            SHELL_OPTS="-f"
            ;;
        ksh)
            SHELL_OPTS="-p"
            if [ "$color_prompt" = yes ] ; then
                PS1="$(tput rev)($SAGE_SHPROMPT_PREFIX)$(tput sgr0) $USER@`hostname -s`:\${PWD##*/}$ "
            else
                PS1="($SAGE_SHPROMPT_PREFIX) $USER@`hostname -s`:\${PWD##*/}$ "
            fi
            export PS1
            ;;
        sh)
            # We don't really know which shell "sh" is (it could be
            # bash, but this is not guaranteed), so we don't set
            # SHELL_OPTS.
            if [ "$color_prompt" = yes ] ; then
                PS1="$(tput rev)($SAGE_SHPROMPT_PREFIX)$(tput sgr0) $USER@`hostname -s`:\${PWD##*/}$ "
            else
                PS1="($SAGE_SHPROMPT_PREFIX) $USER@`hostname -s`:\${PWD}$ "
            fi
            export PS1
            ;;
        tcsh)
            # tcsh doesn't seem to allow the specification of a different
            # .tcshrc file, and the prompt can only be set in this file, so
            # don't bother changing the prompt.
            SHELL_OPTS="-f"
            ;;
        zsh)
            PS1="%S($SAGE_SHPROMPT_PREFIX)%s %n@%m:%~$ "
            # In zsh, the system /etc/zshenv is *always* run,
            # and this may change the path (like on OSX), so we'll
            # create a temporary .zshenv to reset the path
            ZDOTDIR=$DOT_SAGE && export ZDOTDIR
            cat >"$ZDOTDIR/.zshenv" <<EOF
PATH="$PATH" && export PATH
EOF
            SHELL_OPTS=" -d"
            export PS1
            ;;
        *)
            export PS1='($SAGE_SHPROMPT_PREFIX) $ '
            ;;
    esac
    if [ -n "$oldPS1" ]; then
        PS1="$oldPS1"
        export PS1
    fi
    if [ $# -eq 0 ]; then
        # No arguments, so print informative message...
        echo >&2
        echo >&2 "Starting subshell with Sage environment variables set.  Don't forget"
        echo >&2 "to exit when you are done.  Beware:"
        echo >&2 " * Do not do anything with other copies of Sage on your system."
        echo >&2 " * Do not use this for installing Sage packages using \"sage -i\" or for"
        echo >&2 "   running \"make\" at Sage's root directory.  These should be done"
        echo >&2 "   outside the Sage shell."
        echo >&2
        if [ -n "$SHELL_OPTS" ]; then
            echo >&2 "Bypassing shell configuration files..."
            echo >&2
        fi
        echo >&2 "Note: SAGE_ROOT=$SAGE_ROOT"
        "$SHELL" $SHELL_OPTS "$@"
        status=$?
        echo "Exited Sage subshell." 1>&2
    else
        exec "$SHELL" $SHELL_OPTS "$@"
        # If 'exec' returns, an error occurred:
        status=$?
        echo >&2 "Fatal error: 'exec \"$SHELL\" \"$@\"' failed!"
    fi
    exit $status
fi

#####################################################################
# File conversion
#####################################################################

if [ "$1" = '-rst2ipynb' -o "$1" = '--rst2ipynb' ]; then
    shift
    rst2ipynb --kernel=sagemath "$@"
    status="${?}"
    if [ "${status}" -eq "127" ] ; then echo 'rst2ipynb is not installed, please run "sage -i rst2ipynb"' ; fi
    exit ${status}
fi

if [ "$1" = '-ipynb2rst' -o "$1" = '--ipynb2rst' ]; then
    shift
    exec sage-ipynb2rst "$@"
fi

if [ "$1" = '-sws2rst' -o "$1" = '--sws2rst' ]; then
    shift
    exec sage-sws2rst "$@"
fi

#####################################################################
# The notebook, grep, building Sage, testing Sage
#####################################################################

# build_sage, sage -b, sage -br, etc. could be moved to
# build/bin/sage-site. See #29111.

build_sage() {
    maybe_sage_location
    ( cd "$SAGE_ROOT/build/make" && ./install sagelib-no-deps ) || exit $?
}

if [[ "$1" =~ ^--notebook=.* || "$1" =~ ^-n=.* || "$1" =~ ^-notebook=.* ]] ; then
    sage-cleaner &>/dev/null &
    exec sage-notebook "$@"
fi

if [ "$1" = "-notebook" -o "$1" = '--notebook' -o "$1" = '-n' ]; then
    sage-cleaner &>/dev/null &
    exec sage-notebook "$@"
fi

if [ "$1" = "-bn" -o "$1" = "--build-and-notebook" ]; then
    shift
    build_sage
    sage-cleaner &>/dev/null &
    exec sage-notebook --notebook=default "$@"
fi

if [ -n "$SAGE_SRC" -a -d "$SAGE_SRC" ]; then
    # Source inspection facilities, supported on sage-the-distribution and on distributions
    # that package the Sage sources.
    if [ "$1" = '-grep' -o "$1" = "--grep" -o "$1" = "-search_src" -o "$1" = "--search_src" ]; then
        shift
        sage-grep "$@"
        exit 0
    fi

    if [ "$1" = '-grepdoc' -o "$1" = "--grepdoc" -o "$1" = "-search_doc" -o "$1" = "--search_doc" ]; then
        shift
        sage-grepdoc "$@"
        exit 0
    fi
fi

if [ "$1" = '-b' ]; then
    build_sage
    exit $?
fi

if [ "$1" = '-br' -o "$1" = "--br" ]; then
    build_sage
    interactive_sage
fi

if [ "$1" = '-r' ]; then
    shift
    interactive_sage
fi

if [ "$1" = '-ba-force' -o "$1" = '--ba-force' ]; then
    echo
    echo "WARNING: 'sage --ba-force' is deprecated; use 'sage -ba' instead."
    echo
    ( cd "$SAGE_ROOT/build/make" && make sagelib-clean )
    build_sage
    exit $?
fi

if [ "$1" = '-ba' ]; then
    ( cd "$SAGE_ROOT/build/make" && make sagelib-clean )
    build_sage
    exit $?
fi

exec-runtests() {
    sage_setup
    export PYTHONIOENCODING="utf-8"  # Fix encoding for doctests
    exec sage-runtests "$@"
}

if [ "$1" = '-t' -o "$1" = '-bt' -o "$1" = '-tp' -o "$1" = '-btp' ]; then
    if [ "$1" = '-bt' -o "$1" = '-btp' ]; then
        build_sage
    fi
    if [ "$1" = '-tp' -o "$1" = '-btp' ]; then
        shift
        exec-runtests -p "$@"
    else
        shift
        exec-runtests "$@"
    fi
fi

if [ "$1" = '-tnew' -o "$1" = '-btnew' ]; then
    if [ "$1" = '-btnew' ]; then
        build_sage
    fi
    shift
    exec-runtests --new "$@"
fi

if [ "$1" = '-testall' -o "$1" = "--testall" ]; then
    shift
    exec-runtests -a "$@"
fi

if [ "$1" = '-fixdoctests' -o "$1" = '--fixdoctests' ]; then
    shift
    exec sage-fixdoctests "$@"
fi

if [ "$1" = "-coverage" -o "$1" = "--coverage" ]; then
    shift
    exec sage-coverage "$@"
fi

if [ "$1" = "-coverageall" -o "$1" = "--coverageall" ]; then
    shift
    exec sage-coverage --all "$@"
fi

if [ "$1" = '-startuptime' -o "$1" = '--startuptime' ]; then
    exec sage-startuptime.py "$@"
fi

if [ "$1" = '-tox' -o "$1" = '--tox' ]; then
    shift
    if [ -n "$SAGE_SRC" -a -f "$SAGE_SRC/tox.ini" ]; then
        if command -v tox >/dev/null ; then
            exec tox -c "$SAGE_SRC" "$@"
        else
            echo "Run sage -i tox to install"
        fi
    else
        echo >&2 "error: Sage source directory or tox.ini not avialable"
        exit 1
    fi
fi

#####################################################################
# Creating and handling Sage distributions
#####################################################################

# The following could be moved to build/bin/sage-site. See #29111.

if [ "$1" = '--location' ]; then
    maybe_sage_location
    exit 0
fi


install() {
    maybe_sage_location

    for PKG in "$@"
    do
        # Check for options
        case "$PKG" in
            -*)
                INSTALL_OPTIONS="$INSTALL_OPTIONS $PKG"
                continue;;
        esac

        PKG_NAME=`echo "$PKG" | sed -e "s/\.spkg$//"`
        PKG_NAME=`basename "$PKG_NAME"`

        sage-logger \
            "sage-spkg $INSTALL_OPTIONS '$PKG'" "$SAGE_LOGS/$PKG_NAME.log"
        # Do not try to install further packages if one failed
        if [ $? -ne 0 ]; then
            exit 1
        fi
    done
    exit 0
}

if [ "$1" = '-installed' -o "$1" = "--installed" ]; then
    shift
    exec sage-list-packages all --installed-only $@
fi

if [ "$1" = '-p' ]; then
    shift
    # If there are no further arguments, display usage help.
    if [ $# -eq 0 ]; then
        exec sage-spkg
    fi
    install "$@"
fi

if [ "$1" = '-sdist' -o "$1" = "--sdist" ]; then
    maybe_sage_location
    shift
    exec sage-sdist "$@"
fi

#####################################################################
# Debugging tools
#####################################################################

if [ "$1" = '-gdb' -o "$1" = "--gdb" ]; then
    shift
    sage_setup
    if [ "$SAGE_DEBUG" = "no" ]; then
        gdb -x "${SELF}-gdb-commands" \
            -args python "${SELF}-ipython" "$@" -i
    else
        sage_dir=$(sage-python -c 'import os, sage; print(os.path.dirname(sage.__file__))')
        cygdb3 "$sage_dir" "$SAGE_SRC/sage" \
            -- -x "${SELF}-gdb-commands" \
            -args python "${SELF}-ipython" "$@" -i
    fi
    exit $?
fi

if [ "$1" = '-valgrind' -o "$1" = "--valgrind" -o "$1" = '-memcheck' -o "$1" = "--memcheck" ]; then
    shift
    sage_setup
    exec sage-valgrind "$@"
fi

if [ "$1" = '-massif' -o "$1" = "--massif" ]; then
    shift
    sage_setup
    exec sage-massif "$@"
fi

if [ "$1" = '-cachegrind' -o "$1" = "--cachegrind" ]; then
    shift
    sage_setup
    exec sage-cachegrind "$@"
fi

if [ "$1" = '-callgrind' -o "$1" = "--callgrind" ]; then
    shift
    sage_setup
    exec sage-callgrind "$@"
fi

if [ "$1" = '-omega' -o "$1" = "--omega" ]; then
    shift
    sage_setup
    exec sage-omega "$@"
fi

if [ "$1" = '-gthread' -o "$1" = '-qthread' -o "$1" = '-q4thread' -o "$1" = '-wthread' -o "$1" = '-pylab' -o "$1" = '--simple-prompt' -o "$1" = '-simple-prompt' ]; then
    # Intentionally no "shift" here
    interactive_sage "$@"
fi

case "$1" in
    -*)
        # Delegate further option handling to the non-installed sage-site script.
        # (These options become unavailable if the directory $SAGE_ROOT is removed.)
        if [ -n "$SAGE_ROOT" ]; then
            exec "$SAGE_ROOT/build/bin/sage-site" "$@"
            # fallthrough if there is no sage-site script
        fi
        echo "Error: unknown option: $1"
        exit 1
        ;;
esac

if [ $# -ge 1 ]; then
    T=`echo "$1" | sed -e "s/.*\.//"`
    if [ "$T" = "spkg" ]; then
        echo "Error: Installing old-style SPKGs is no longer supported."
        exit 1
    fi
    sage_setup
    unset TERM  # See Trac #12263
    # sage-run rejects all command line options as the first argument.
    exec sage-run "$@"
fi

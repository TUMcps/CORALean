# Sourced, not run: `. "$root/scripts/find-python.sh"` sets `PYTHON` to the first
# of `python3`, `python` that is a working Python 3.8 or later, or says so and
# exits the sourcing script with status 2.
#
# Naming the first one that exists is not enough. On Windows `python3` is by
# default a Microsoft Store stub that is found on `PATH`, prints a hint, and
# runs nothing, so the check that called it silently checked nothing; running a
# one-line program and reading its answer is what tells a stub from an interpreter. `py -3`, the
# Windows launcher, is the last candidate.

PYTHON=
for candidate in python3 python "py -3"; do
  # unquoted on purpose: `py -3` is a command and an argument
  # it must also say so: a stand-in that exits 0 without running anything passes `sys.exit`
  if [ "$($candidate -c 'import sys; print(sys.version_info >= (3, 8))' 2>/dev/null)" = True ]; then
    PYTHON=$candidate
    break
  fi
done
if [ -z "$PYTHON" ]; then
  echo "error: no working Python 3.8 or later (tried python3, python, py -3)." >&2
  echo "       On Windows, install Python and turn off the 'python3' app execution alias" >&2
  echo "       (Settings > Apps > Advanced app settings > App execution aliases)." >&2
  exit 2
fi

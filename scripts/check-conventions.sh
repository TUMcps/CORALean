#!/bin/sh
# Checks the conventions CONTRIBUTING.md states, none of which the compiler can
# check: a green build says nothing about whether `aux_` stayed in its file or
# whether an `API.lean` slipped a declaration in.
#
# Text only — no Lean, no build, no network, so it is cheap enough to run on a
# pre-commit hook as well as in CI: about fifteen seconds over the whole tree
# on Linux (the per-file pass is three fifths of that, the `Basic.lean` bundles
# a fifth), and a fraction of a second on `--staged`. That is why the parsing is
# deliberately shallow: comments are stripped by a two-character scanner and
# declarations are matched at the start of a line. It reports what is wrong,
# never rewrites.
#
#   sh scripts/check-conventions.sh                  the whole tree (CI)
#   sh scripts/check-conventions.sh --staged LIST    the per-file rules only, on
#                                                    the index version of the
#                                                    `src/**/*.lean` paths in LIST
#
# `--staged` is what `.githooks/pre-commit` runs for a commit that cannot change
# a cross-file rule. It leaves out everything that reads other files than the
# ones given: reachability, the layout, the collectors' completeness, the float
# layer's type names, layering, the import guards, the allowlists' stale-entry
# reports and the `Basic.lean` exceptions' import cycles. It is not a way to
# check less: `.githooks/pre-commit` decides, with `scripts/precommit-scope.py`,
# when one of those rules could notice the commit, and then runs the whole tree.
#
# POSIX sh and awk, so it runs in CI and in Git Bash on Windows alike, and one
# Python helper for the `Basic.lean` bundles, `scripts/check-basic-bundles.py`,
# found by `scripts/find-python.sh`.

set -eu

# Byte semantics everywhere, so the checks read the same under gawk and mawk;
# `charlen` is what turns bytes back into characters where that is what is
# meant. Without this a line of ℝ and ⊆ counts as over-long in CI and not here.
LC_ALL=C
export LC_ALL

cd "$(dirname "$0")/.."
repo=$(pwd)

STAGED=
case "${1:-}" in
  "") ;;
  --staged)
    [ $# -eq 2 ] || { echo "usage: check-conventions.sh [--staged LIST]" >&2; exit 2; }
    STAGED=$2 ;;
  *) echo "usage: check-conventions.sh [--staged LIST]" >&2; exit 2 ;;
esac

# The interpreter for the Python helper, found before any check runs: a missing
# one is an error here, never an empty report.
. "$repo/scripts/find-python.sh"

# The numeric limits, gathered here because every one of them is a judgement
# call and the tree is the evidence for it. Each is at or just above the trimmed
# tree's worst case, so raising one is a decision rather than a drift.
MAX_LINE=100          # characters, not bytes
MAX_MODULE_DOC=20     # module docstring, content file
MAX_COLLECTOR_DOC=25  # module docstring, collector: it is the directory entry point
MAX_DECL_DOC=3        # docstring ahead of a declaration
MAX_LINES_WO_COMMENT=20  # a minimum density, not a maximum: proofs need signposts
MAX_PUBLIC_DECL=1     # public declarations per `Operations/`/`Theorems/` file (#62)
# `Counterexamples/` (#148) is outside that rule: a CORA model and its refutations share a file,
# and so does the module docstring's cap, once for each `# ` title a part of the file brings.

# The one file that may carry an `axiom`. `Float` is opaque in Lean's logic, so
# the native binary64 backend has to assume what the hardware does; every other
# file in the tree proves what it states, and naming the exception here is what
# keeps it one file rather than a habit.
AXIOM_FILE=src/CORALean/Global/Float/Instances/Binary64/Definitions/Axioms.lean

# The other file, and the opposite case: `nearestUnsound`, the bench's
# round-to-nearest baseline, FALSE by design so that the unchanged library runs
# on what CORA computes with. Tolerable only while nothing but the bench can
# reach it, so that file may declare this one name and nothing else, and a file
# outside `BENCH_DIR` that imports a `NearestUnsound` module is refused.
# `scripts/check-axioms.sh` asks Lean the same question of the proof terms.
NEAREST_AXIOM_FILE=src/CORALean/Examples/Bench/NearestUnsound/Axioms.lean
NEAREST_AXIOM=nearestUnsound

# The third, true like the first: `trustedFlint`, that FLINT's `arf_*` calls
# round as documented, assumed by the optional FLINT backend. That file may
# declare this one name and nothing else.
FLINT_AXIOM_FILE=src/CORALean/Global/Float/Instances/Flint/Definitions/Axioms.lean
FLINT_AXIOM=trustedFlint
BENCH_DIR=src/CORALean/Examples/Bench/

# `noncomputable` outside a representation's `Real/` layer, the scalar
# interface's instance at ℝ and a `Definitions/` file is legitimate only for an
# `aux_` declaration or a name listed here with a reason — see the file's own
# header for what a reason must say. The name is the declaration's own,
# exactly as written after `noncomputable` — a dotted prefix and all, so a
# bare `reach` here excuses only a bare `reach`, never `LinearSys.reach` too.
# Under `Float/` even that allowlist does not reach: only the `aux_` exemption
# does, because the whole point of the float layer is that it runs.
ALLOWLIST=scripts/noncomputable-allowlist.txt

# A `...Cost` under `Complexity/Time/` that is `0` says the operation writes nothing and computes
# nothing (CONTRIBUTING, "Complexity"): under `Global/Cost.lean`'s model every scalar of a result
# is a write, so building an object is never free. An operation that really does neither names
# itself in this list, `<qualified name>  <reason>` per line. The list only shrinks: an entry
# whose definition is no longer a zero cost is reported as stale.
ZEROCOST_LIST=scripts/zero-cost-allowlist.txt

# Every file under `src/` is a Lean `module` (CONTRIBUTING, "The module
# header") except the worked examples under `Examples/`, whose `#eval`s would
# need `meta import`, and the files listed here with a reason: proofs that
# unfold a definition Mathlib or core does not expose, and the files that import
# one (a module cannot import a non-module). The list only shrinks: an entry
# that is a module now, or is gone, is reported as stale.
NONMODULE_LIST=scripts/non-module-allowlist.txt

# Pairs `ℝ × ℝ`, `𝕋 × 𝕋`, `α × α`, `EReal × EReal`, and structures with sibling fields named
# `…Inf`/`…Sup`, `…Lo`/`…Hi` or `lo…`/`hi…` (CONTRIBUTING, "Bounds of one quantity"): the lower
# and the upper bound of one quantity are an `Interval`, so a file that still spells such a
# pair names why in this list, `<path>  <reason>` per line. `Examples/` is exempt: it is
# input and output, where a pair is a datum. The list only shrinks, as the one above.
PAIR_LIST=scripts/pair-allowlist.txt

# Interfaces (#177): a `class` is declared only in a file named `Interfaces.lean`, which is what a
# class root's `Instances.lean` instantiates, so the interfaces a directory offers are one file to
# read. A file that declares one elsewhere names why in this list, `<path>  <reason>` per line.
# The list only shrinks: an entry whose file declares no class any more is reported as stale.
CLASS_LIST=scripts/class-allowlist.txt

# `Operations/` holds definitions, never theorems (#198), the mirror of the rule that keeps
# definitions out of `Theorems/`: a theorem in an `Operations/` file is a guarantee about the
# operation, which is a `Theorems/` file's to state, or a general fact, which is a global lemma's
# (or, with one user, a `private` lemma there). A file that still declares one is listed in this
# file, `<path>` per line with `#` comments, until it is moved. The list only shrinks: an entry
# whose file declares no theorem any more is reported as stale.
OPS_THEOREM_LIST=scripts/operations-theorem-allowlist.txt

# Rule A. A class root, a directory holding an `Operations/`, `Theorems/` or
# `Definitions/` folder, holds its class file, `Interfaces.lean`, `Instances.lean` and `API.lean`
# and nothing else: every other file has a role folder beside them. Which of
# the remaining files is the class file is not guessed at, so the rule is that
# there is at most one.

# Class roots not yet sorted into role folders, one per line. The list only
# shrinks: an entry whose directory now passes, or is gone, is reported the way
# a stale allowlist entry is.
CLASS_ROOT_PENDING="
"

# Layering (CONTRIBUTING, "Import guards and layering"). One line per importing
# top-level directory of `src/CORALean/`: `Dir: Dir Dir …`, the directories it
# may not import. Measured on the tree, not wished for: `ContDynamics`, `NN` and
# `Specification` import one another (a neural-network controller is a dynamics,
# a dynamics has a specification), so those pairs are left out until that cycle
# is cut. `Examples/` imports anything and nothing imports it. Whoever adds a
# line here has checked that the tree already satisfies it.
LAYERS="
Global: ContSet ContDynamics DiscrDynamics HybridDynamics NN Specification Examples
ContSet: ContDynamics DiscrDynamics HybridDynamics NN Specification Examples
DiscrDynamics: ContDynamics HybridDynamics NN Specification Examples
ContDynamics: HybridDynamics Examples
NN: HybridDynamics Examples
Specification: NN HybridDynamics Examples
HybridDynamics: Examples
"

# The imports the table forbids that the tree has, one per line as
# `file | directory | reason`; a reason says why the code is not elsewhere. The
# list only shrinks: an entry whose file no longer imports that directory is
# reported as stale.
LAYER_EXCEPTIONS="
src/CORALean/ContSet/ProbZonotope/Float/Theorems/EncloseMeanOuter.lean | ContDynamics | encloses the mean with the matrix-exponential enclosure that lives with LinearSys
src/CORALean/ContSet/ProbZonotope/Float/Operations/Enclose.lean | ContDynamics | encloses the mean with the matrix-exponential enclosure that lives with LinearSys
src/CORALean/ContSet/ProbZonotope/Real/Theorems/GaussPdfExpMulVec.lean | ContDynamics | the Gaussian density under exp(At) uses the determinant of the matrix exponential
src/CORALean/ContSet/Zonotope/Real/Counterexamples/FaultObservePRadius.lean | ContDynamics | counterexample to the fault-radius LMI, which is defined with LinearSysDT
src/CORALean/Global/Float/DivFact.lean | ContSet/Interval | q / k! is an enclosure, so it is a Float.Interval, the type of the very enclosures it feeds; imports ContSet/Interval/Float/Interval only, which needs nothing above Global/Float/SoundFloatArithmetic
src/CORALean/Global/Float/InverseTrig.lean | ContSet/Interval | the arctangent bracket is an enclosure, so it is a Float.Interval, the type of the enclosures built from it; imports ContSet/Interval/Float/Interval only, which needs nothing above Global/Float/SoundFloatArithmetic
src/CORALean/Global/Float/RatUp.lean | ContSet/Interval | the bracket around a natural number is an enclosure, so it is a Float.Interval; imports ContSet/Interval/Float/Interval only, which needs nothing above Global/Float/SoundFloatArithmetic
src/CORALean/Global/Float/SinCos.lean | ContSet/Interval | the sine and cosine seeds are enclosures, so they are Float.Intervals, the type of the enclosures built from them; imports ContSet/Interval/Float/Interval only, which needs nothing above Global/Float/SoundFloatArithmetic
src/CORALean/Global/Float/TrigRange.lean | ContSet/Interval | the sine and cosine over a range are enclosures, so they are Float.Intervals, the type of the enclosures built from them; imports ContSet/Interval/Float/Interval only, which needs nothing above Global/Float/SoundFloatArithmetic
"

# The base files: imported by so much of the tree that what creeps into their
# closure rebuilds it. Each carries `assert_not_exists` / `assert_not_imported`
# guards, `file | number of guards`; changing a count is deleting or adding a
# guard on purpose.
GUARDED_FILES="
src/CORALean/Global/Tensor.lean | 8
src/CORALean/Global/Entrywise.lean | 8
src/CORALean/Global/Scalar.lean | 8
src/CORALean/Global/Float/FloatOps.lean | 8
src/CORALean/ContSet/ContSet/Interfaces.lean | 10
src/CORALean/ContSet/Interval/Real/Interval.lean | 8
"

# Counterexamples (#148). A refutation and a model of CORA's code as printed live in a `Counterexamples/`
# folder, which holds nothing else, and no file name ends in `Counterexample` (the folder says it). A
# file that the rule would send there but the library imports stays where it is, listed here as
# `file | reason`: a CORA model that a library theorem states on purpose (CORA's rank test of
# `isFullDim`, which `IsFullDimRank` proves necessary), or a theorem about the corrected counterexample
# of the paper. Where the library has a better or exact version it uses that, and the CORA model lives in
# `Counterexamples/`. The list only shrinks.
COUNTEREXAMPLE_EXCEPTIONS="
src/CORALean/ContSet/ConPolyZono/Real/Operations/IsFullDimCora.lean | IsFullDimRank proves CORA's rank test necessary for a set with an interior point (the same test, via the polynomial zonotope's): a theorem about CORA's own test, on purpose, so no other version can take its place
src/CORALean/ContSet/PolyZonotope/Real/Operations/IsFullDimCora.lean | IsFullDimRank proves CORA's rank test necessary for a set with an interior point (the test is necessary): a theorem about CORA's own test, on purpose, so no other version can take its place
src/CORALean/ContDynamics/LinearSys/Operations/SupportCounterexample.lean | the corrected counterexample of [1, Sec. 4.2], which the verification search extracts a run from; a repair, not a refutation
src/CORALean/ContDynamics/LinearSys/Theorems/HeldSimSupportCounterexample.lean | the corrected counterexample reaches the lower bound exactly; a repair that other theorems use
src/CORALean/ContDynamics/LinearSys/Theorems/HeldSimLeSupportCounterexample.lean | the corrected counterexample is a support vector; a repair that other theorems use
"

status=0

report() {
  if [ -n "$1" ]; then
    printf '%s\n' "$1"
    status=1
  fi
}

# The entry points the build is told to start from: `roots = [...]` of each
# `[[lean_lib]]` and `root = ...` of each `[[lean_exe]]`. They are the one place
# outside a collector that may import a collector.
lake_roots=$(sed -n 's/^roots[[:space:]]*=[[:space:]]*\[\(.*\)\].*/\1/p; s/^root[[:space:]]*=[[:space:]]*\(.*\)/\1/p' lakefile.toml |
  grep -o '"[^"]*"' | tr -d '"' | tr '\n' ' ')

if [ -n "$STAGED" ]; then
  # The index version of each listed file, checked out beside nothing else: the
  # per-file rules read one file at a time, so this is the whole input they need.
  # Run from inside it, the paths in the messages are the repository's own. What
  # lives outside `src/` is read from the checkout, which the hook has already
  # sent down the full path when the commit changes any of it.
  files=$(sed 's#\\#/#g' "$STAGED" | grep -E '^src/.*[.]lean$' | sort -u || true)
  if [ -z "$files" ]; then
    printf 'conventions: no staged file under src/, nothing to check\n'
    exit 0
  fi
  ALLOWLIST=$repo/$ALLOWLIST
  ZEROCOST_LIST=$repo/$ZEROCOST_LIST
  NONMODULE_LIST=$repo/$NONMODULE_LIST
  PAIR_LIST=$repo/$PAIR_LIST
  CLASS_LIST=$repo/$CLASS_LIST
  OPS_THEOREM_LIST=$repo/$OPS_THEOREM_LIST
  FAMILY_LONG_FORM_OK=$repo/${FAMILY_LONG_FORM_OK:-scripts/family-notation-exceptions.txt}
  stage=$(mktemp -d)
  printf '%s\n' "$files" | git checkout-index --prefix="$stage/" --stdin
  cd "$stage"
else
  files=$(find src -name '*.lean' | sed 's#\\#/#g' | sort)
fi

# The file list reaches awk through a list file rather than the command line,
# for every pass below, not only the two that are global by nature. `xargs`
# splits an argument list that does not fit — on Windows the limit is 32 KB,
# and the environment a git hook adds is enough to cross it at this repository
# size — and the allowlist's stale-entry report is global exactly the way the
# reachability check is: a split would see only one batch's declarations and
# call every entry the other batch owns stale.
list=$(mktemp)
cexlist=$(mktemp)
trap 'rm -f "$list" "$cexlist"; [ -z "${stage:-}" ] || rm -rf "$stage"' EXIT INT TERM
printf '%s\n' "$files" > "$list"
printf '%s\n' "$COUNTEREXAMPLE_EXCEPTIONS" > "$cexlist"

# Per-file conventions, one pass, plus the allowlist's own stale-entry report
# at the end, which needs every file's declarations to have been seen.
# `depth` tracks nesting of `/- -/` across lines, so a docstring mentioning
# `aux_` or `sorry` is not mistaken for code.
out=$(awk \
  -v LIST="$list" \
  -v MAX_LINE="$MAX_LINE" \
  -v MAX_MODULE_DOC="$MAX_MODULE_DOC" \
  -v MAX_COLLECTOR_DOC="$MAX_COLLECTOR_DOC" \
  -v MAX_DECL_DOC="$MAX_DECL_DOC" \
  -v MAX_LINES_WO_COMMENT="$MAX_LINES_WO_COMMENT" \
  -v MAX_PUBLIC_DECL="$MAX_PUBLIC_DECL" \
  -v AXIOM_FILE="$AXIOM_FILE" \
  -v NEAREST_AXIOM_FILE="$NEAREST_AXIOM_FILE" \
  -v NEAREST_AXIOM="$NEAREST_AXIOM" \
  -v FLINT_AXIOM_FILE="$FLINT_AXIOM_FILE" \
  -v FLINT_AXIOM="$FLINT_AXIOM" \
  -v BENCH_DIR="$BENCH_DIR" \
  -v LAKE_ROOTS="$lake_roots" \
  -v NONMOD="$NONMODULE_LIST" \
  -v PAIRLIST="$PAIR_LIST" \
  -v ZEROLIST="$ZEROCOST_LIST" \
  -v CEXLIST="$cexlist" \
  -v STALE="$([ -z "$STAGED" ] && echo 1 || echo 0)" \
  -v ALLOWLIST="$ALLOWLIST" '
# One `Reviewed:` entry: `DD-Month-YYYY (Name)`, a human name.
function checkReview(val, ln,    d, nm) {
  if (val !~ /^[0-9][0-9]-[A-Za-z]+-[0-9][0-9][0-9][0-9] \(.+\)$/) {
    say(FILENAME ":" ln ": `Reviewed:` is `---` or lines `DD-Month-YYYY (Name)`, not `" val "`")
    return
  }
  d = val; sub(/ .*$/, "", d)
  nm = val; sub(/^[^(]*\(/, "", nm); sub(/\)$/, "", nm)
  if (d !~ DATE)
    say(FILENAME ":" ln ": `Reviewed:` date `" d "` is not a DD-Month-YYYY date")
  if (nm ~ /^Claude/)
    say(FILENAME ":" ln ": `Reviewed:` records human reviews — `" nm "` is a model")
}

BEGIN {
  while ((getline f < LIST) > 0) if (f != "") ARGV[ARGC++] = f
  CONT = "[\200-\277]"
  MONTH = "(January|February|March|April|May|June|July|August|September|October|November|December)"
  DATE = "^(0[1-9]|[12][0-9]|3[01])-" MONTH "-[0-9][0-9][0-9][0-9]$"

  # The allowlist: `<qualified name>  <reason>` per line, `#` comments and
  # blank lines ignored. `allowLine` is kept for the stale-entry report at
  # the end.
  while ((getline aline < ALLOWLIST) > 0) {
    allowFNR++
    line = aline
    sub(/^[ \t]+/, "", line)
    if (line == "" || line ~ /^#/) continue
    name = line
    sub(/[ \t].*$/, "", name)
    # One line per name: a merge that keeps an old reason beside a new one
    # (a stale `pending` next to its `real-layer`) inflates every count read here.
    if (name in allowNC)
      say(ALLOWLIST ":" allowFNR ": duplicate allowlist entry `" name "` (first at line " allowLine[name] ")")
    allowNC[name] = 1
    allowLine[name] = allowFNR
  }
  close(ALLOWLIST)

  # The zero-cost list: `<qualified name>  <reason>` per line, as the allowlist above.
  while ((getline zline < ZEROLIST) > 0) {
    zeroFNR++
    line = zline
    sub(/^[ \t]+/, "", line)
    if (line == "" || line ~ /^#/) continue
    zn = line; sub(/[ \t].*$/, "", zn)
    zr = line; sub(/^[^ \t]+[ \t]*/, "", zr)
    if (zn in zeroOK)
      say(ZEROLIST ":" zeroFNR ": duplicate entry `" zn "` (first at line " zeroLine[zn] ")")
    if (zr == "")
      say(ZEROLIST ":" zeroFNR ": `" zn "` carries no reason — say what the operation neither" \
          " computes nor writes")
    zeroOK[zn] = 1
    zeroLine[zn] = zeroFNR
  }
  close(ZEROLIST)

  # The non-module list: `<path>  <reason>` per line, as the allowlist above.
  while ((getline nline < NONMOD) > 0) {
    nmFNR++
    line = nline
    sub(/^[ \t]+/, "", line)
    if (line == "" || line ~ /^#/) continue
    p = line; sub(/[ \t].*$/, "", p)
    r = line; sub(/^[^ \t]+[ \t]*/, "", r)
    if (p in nonmodOK)
      say(NONMOD ":" nmFNR ": duplicate entry `" p "` (first at line " nonmodLine[p] ")")
    if (r == "")
      say(NONMOD ":" nmFNR ": `" p "` carries no reason — say why it cannot be a module")
    nonmodOK[p] = 1
    nonmodLine[p] = nmFNR
  }
  close(NONMOD)

  # The pair list: `<path>  <reason>` per line, as the non-module list above.
  while ((getline pline < PAIRLIST) > 0) {
    pairFNR++
    line = pline
    sub(/^[ \t]+/, "", line)
    if (line == "" || line ~ /^#/) continue
    p = line; sub(/[ \t].*$/, "", p)
    r = line; sub(/^[^ \t]+[ \t]*/, "", r)
    if (p in pairOK)
      say(PAIRLIST ":" pairFNR ": duplicate entry `" p "` (first at line " pairLine[p] ")")
    if (r == "")
      say(PAIRLIST ":" pairFNR ": `" p "` carries no reason — say why its pair is not an interval")
    pairOK[p] = 1
    pairLine[p] = pairFNR
  }
  close(PAIRLIST)

  # The counterexample exceptions: `<path> | <reason>` per line.
  while ((getline cline < CEXLIST) > 0) {
    if (cline !~ /[^ \t]/) continue
    cpath = cline; sub(/[ \t]*\|.*$/, "", cpath); sub(/^[ \t]+/, "", cpath)
    if (cline !~ /\|[ \t]*[^ \t]/)
      say("scripts/check-conventions.sh: COUNTEREXAMPLE_EXCEPTIONS entry `" cpath "` carries no reason")
    cexOK[cpath] = 1
  }
  close(CEXLIST)

  # An import line in any of the forms a module may write it; the prefixes are
  # what `public`/`meta` add, and a non-module may use neither.
  IMPORT = "^(public[ \t]+)?(meta[ \t]+)?import[ \t]+"

  # A declaration, optionally carrying one attribute — `@[simp] theorem …` is as
  # much a declaration as `theorem …`, and every rule that scans for one needs to
  # see both alike. Built from octal escapes, not `\\[` `\\]` literals: this
  # awk drops a backslash ahead of a bracket in a string constant instead of
  # keeping it escaped, silently turning the pattern into a character class.
  BSLASH = "\134"; LBRACK = "\133"; RBRACK = "\135"
  ATTR = "(@" BSLASH LBRACK "[^" RBRACK "]*" BSLASH RBRACK "[ \t]*)?"
  MODS = "(private |protected |noncomputable |partial |scoped )*"
  KIND = "(def|theorem|lemma|abbrev|instance|structure|inductive|class|opaque)"
  DECL_START = "^" ATTR MODS KIND " "
  DECL_PREFIX = "^" ATTR MODS KIND "[ \t]+"

  # The four section markers stamped across every file with declarations:
  # exactly 100 characters, `-` fill except the label naming the main
  # declaration, which uses `=`. Checked by exact string match against every
  # valid form rather than by a width-only regex, so a marker that is 100
  # characters but has its fill split unevenly around the label — a mistake a
  # length check alone would miss — is still caught.
  M_BEGIN = "-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --"
  M_AUX   = "-- ----------------------------------------  AUXILIARY  ----------------------------------------- --"
  M_END   = "-- ---------------------------------------  END OF CODE  ---------------------------------------- --"
  M_THM   = "-- =======================================  MAIN THEOREM  ======================================= --"
  M_DEF   = "-- =====================================  MAIN DEFINITION  ====================================== --"
  M_INST  = "-- ======================================  MAIN INSTANCE  ======================================= --"
  M_TYPE  = "-- ========================================  MAIN TYPE  ========================================= --"
  M_INSTS = "-- ========================================  INSTANCES  ========================================= --"
  # A section of a `Basic.lean` (CONTRIBUTING, "Small declarations"): the
  # declaration it holds, in backticks, in place of a label.
  SECTION_BANNER = "^-- =+  `[^`]+`  =+ --$"

  markerLabel[M_BEGIN] = "BEGIN CODE"
  markerLabel[M_AUX]   = "AUXILIARY"
  markerLabel[M_END]   = "END OF CODE"
  markerLabel[M_THM]   = "MAIN THEOREM"
  markerLabel[M_DEF]   = "MAIN DEFINITION"
  markerLabel[M_INST]  = "MAIN INSTANCE"
  markerLabel[M_TYPE]  = "MAIN TYPE"
  markerLabel[M_INSTS] = "INSTANCES"

  # What a `MAIN ...` marker label must be, given the kind of the
  # declaration that follows it — the rule that stops a label going stale
  # after a refactor changes what the main declaration of a file is.
  mainLabelForKind["theorem"]    = "MAIN THEOREM"
  mainLabelForKind["lemma"]      = "MAIN THEOREM"
  mainLabelForKind["def"]        = "MAIN DEFINITION"
  mainLabelForKind["abbrev"]     = "MAIN DEFINITION"
  mainLabelForKind["opaque"]     = "MAIN DEFINITION"
  mainLabelForKind["instance"]   = "MAIN INSTANCE"
  mainLabelForKind["structure"]  = "MAIN TYPE"
  mainLabelForKind["class"]      = "MAIN TYPE"
  mainLabelForKind["inductive"]  = "MAIN TYPE"
}

# Characters, not bytes: every byte of a UTF-8 sequence but the first is a
# continuation byte, so dropping those counts the characters.
function charlen(s,   t) { t = s; gsub(CONT, "", t); return length(t) }

# Returns the code on the line and, as a side effect, reports what comment
# syntax it passed through: `opened` names the kind of block that started here
# and `sawComment` says whether any comment was on the line at all.
function strip(line,   out, i, c, n, k) {
  out = ""; i = 1; n = length(line)
  sawComment = (depth > 0); opened = ""
  while (i <= n) {
    c = substr(line, i, 2)
    if (depth == 0 && c == "--") { sawComment = 1; break }
    if (c == "/-") {
      depth++; sawComment = 1
      if (depth == 1) {
        k = substr(line, i + 2, 1)
        opened = (k == "!") ? "mod" : ((k == "-") ? "doc" : "blk")
      }
      i += 2; continue
    }
    if (c == "-/") { if (depth > 0) depth--; sawComment = 1; i += 2; continue }
    if (depth == 0) out = out substr(line, i, 1)
    i++
  }
  return out
}

# The first name in `code` that is `tmp` or `temp` or a variant of either (`tmp1`, `temp₂`, `temp_`,
# `tmpX`, a primed `temp`), or "". A name is read whole: `template` and `temporal` are other words, and
# a field access (`x.temp`) is not a binder of ours. Called on code with comments removed and
# string literals blanked, so only code is read. Such a name can only be a binder (`let`, `have`,
# `fun`, an `obtain`/`rcases` pattern, `intro`, an argument of a declaration) or a use of one.
function tmpName(line,   rest, off, pre, nxt, nm, b3, p) {
  rest = line; off = 0
  while (match(rest, /(tmp|temp)([A-Z0-9_\x27][A-Za-z0-9_\x27]*)?/)) {
    p = off + RSTART
    nm = substr(rest, RSTART, RLENGTH)
    pre = (p > 1) ? substr(line, p - 1, 1) : ""
    b3 = (p > 3) ? substr(line, p - 3, 3) : ""
    nxt = substr(rest, RSTART + RLENGTH)
    while (nxt ~ /^\xe2\x82[\x80-\x89]/) { nm = nm substr(nxt, 1, 3); nxt = substr(nxt, 4) }
    if (pre !~ /[A-Za-z0-9_.\x27]/ && (pre !~ /[\x80-\xff]/ || b3 == "⟨" || b3 == "⦃") &&
        nxt !~ /^[A-Za-z0-9_\x27]/)
      return nm
    off += RSTART + RLENGTH - 1; rest = substr(rest, RSTART + RLENGTH)
  }
  return ""
}

function base(name,   k) {
  k = split(name, parts, "\\.")
  return parts[k]
}

# Whether the result type of a declaration header is `Prop` or a `Set`: the text
# after its last colon outside brackets, then after its last arrow outside
# brackets, which is the codomain once every argument is applied.
function propOrSet(h,   i, c, d, cut, t, seg) {
  sub(/:=.*$/, "", h); sub(/ where([ \t].*)?$/, "", h); sub(/[ \t]\|.*$/, "", h)
  d = 0; cut = 0
  for (i = 1; i <= length(h); i++) {
    c = substr(h, i, 1)
    if (c == "(" || c == "{" || c == LBRACK) d++
    else if (c == ")" || c == "}" || c == RBRACK) d--
    else if (c == ":" && d == 0) cut = i
  }
  if (cut == 0) return 0
  t = substr(h, cut + 1); d = 0; seg = t
  for (i = 1; i <= length(t); i++) {
    c = substr(t, i, 1)
    if (c == "(" || c == "{" || c == LBRACK) d++
    else if (c == ")" || c == "}" || c == RBRACK) d--
    else if (d == 0 && substr(t, i, 3) == "→") seg = substr(t, i + 3)
  }
  sub(/^[ \t]+/, "", seg); sub(/[ \t]+$/, "", seg)
  return (seg == "Prop" || seg ~ /^Set([ \t(]|$)/)
}

# Whether the codomain of a declaration header, read as `propOrSet` reads it,
# is an `Option`.
function returnsOption(h,   i, c, d, cut, t, seg) {
  sub(/:=.*$/, "", h); sub(/ where([ \t].*)?$/, "", h)
  d = 0; cut = 0
  for (i = 1; i <= length(h); i++) {
    c = substr(h, i, 1)
    if (c == "(" || c == "{" || c == LBRACK) d++
    else if (c == ")" || c == "}" || c == RBRACK) d--
    else if (c == ":" && d == 0) cut = i
  }
  if (cut == 0) return 0
  t = substr(h, cut + 1); d = 0; seg = t
  for (i = 1; i <= length(t); i++) {
    c = substr(t, i, 1)
    if (c == "(" || c == "{" || c == LBRACK) d++
    else if (c == ")" || c == "}" || c == RBRACK) d--
    else if (d == 0 && substr(t, i, 3) == "→") seg = substr(t, i + 3)
  }
  sub(/^[ \t]+/, "", seg)
  return (seg ~ /^Option([ \t(]|$)/)
}

function moduleOf(path,   m) {
  m = path
  sub(/^src\//, "", m)
  sub(/\.lean$/, "", m)
  gsub("/", ".", m)
  return m
}

function dirOf(path,   d) {
  d = path
  if (d ~ /\//) sub(/\/[^\/]*$/, "", d); else d = ""
  return d
}

function say(msg) { print msg }

# Closes a stretch of uncommented code and reports it if it ran too long.
function endRun(f) {
  if (run > MAX_LINES_WO_COMMENT)
    say(f ":" runStart ": " run " lines of code with no comment, over " \
        MAX_LINES_WO_COMMENT " — a line saying what this step is doing goes here")
  run = 0
}

# Called when the top-level comment block that started on `blockStart` ends.
function closeBlock(e,   len) {
  len = e - blockStart + 1
  if (blockKind == "mod") {
    # The cap is on the prose. A `## References` block is a bibliography, which
    # does not grow the way an explanation does, so it is measured out.
    if (docLine == 0) {
      docLine = blockStart; docEnd = e
      docLen = (refsLine > 0) ? refsLine - blockStart : len
    }
  } else if (blockKind == "doc") {
    if (len > MAX_DECL_DOC)
      say(FILENAME ":" blockStart ": declaration docstring is " len " lines, over " \
          MAX_DECL_DOC " — move the explanation into the module docstring")
    declDocEnd = e
  } else if (len > 1) {
    say(FILENAME ":" blockStart ": block comment spans " len " lines" \
        " — say it in one line, or move it into the module docstring")
  }
  blockKind = ""
}

function check(f,   i, n, collector, want, dir, cap, nroot, rootList, isRoot) {
  endRun(f)
  collector = (f ~ /\/API\.lean$/) || (f == "src/CORALean.lean")

  for (a in useAux)
    if (!(a in declAux))
      say(f ":" useAux[a] ": `aux_` name `" a "` is not declared in this file")

  if (docLine == 0) {
    say(f ":1: no module docstring — every file opens with `/-! ... -/`")
  } else {
    cap = collector ? MAX_COLLECTOR_DOC : MAX_MODULE_DOC
    if (f ~ /\/Counterexamples\// && nh1 > 1) cap = MAX_MODULE_DOC * nh1
    if (docLen > cap)
      say(f ":" docLine ": module docstring is " docLen " lines, over " cap \
          " — keep what is non-obvious about this file and drop the rest")
  }

  if (collector) {
    if (authorLine > 0)
      say(f ":" authorLine ": a collector carries no author block")
    if (f ~ /\/API\.lean$/ && codeLine > 0)
      say(f ":" codeLine ": `API.lean` holds nothing but imports")
  } else if (isBasic) {
    # every section carries its own block, under its banner
  } else if (authorLine == 0) {
    say(f ":1: no author block — content files carry one, after the module docstring")
  } else if (docLine > 0 && authorLine != docEnd + 2) {
    say(f ":" authorLine ": the author block goes one blank line under the module" \
        " docstring, which ends at line " docEnd)
  }

  # Counterexamples (#148). A refutation or a model of the CORA code lives in a `Counterexamples/`
  # folder, and that folder holds nothing else; no file name ends in `Counterexample`. What a folder
  # holds is told by name and by what the file says, which is as much as text can tell: a file
  # there says `counterexample` or `Cora` somewhere, or is named for CORA, or declares a negated
  # statement (`not_`, `_ne`). `COUNTEREXAMPLE_EXCEPTIONS` lists
  # the files the library imports.
  stemName = f; sub(/^.*\//, "", stemName); sub(/\.lean$/, "", stemName)
  if (f ~ /\/Counterexamples\//) {
    if (stemName ~ /Counterexample$/)
      say(f ":1: a file in `Counterexamples/` is named for the model or the theorem, without the" \
          " `Counterexample` suffix")
    else if (!collector && !cexWord && !cexNeg && stemName !~ /Cora|CORA/)
      say(f ":1: `Counterexamples/` holds refutations and models of the CORA code, and this file" \
          " never says `counterexample` or `Cora`, names no negated theorem (`not_`, `_ne`), and" \
          " is not named for the CORA code")
  } else if (!collector) {
    why = ""
    if (stemName ~ /Counterexample$/) why = "its name ends in `Counterexample`"
    else if (stemName ~ /Cora([^a-z]|$)/) why = "its name says `Cora`"
    else if (cexDecl != "") why = "it declares `" cexDecl "`"
    if (why != "") {
      if (f in cexOK) cexUsed[f] = 1
      else
        say(f ":1: a refutation or a model of the CORA code lives in a `Counterexamples/` folder" \
            " (" why "): move it there without the `Counterexample` suffix, or list it in" \
            " COUNTEREXAMPLE_EXCEPTIONS if the library imports it")
    }
  }

  # The module header, at fixed lines (CONTRIBUTING, "The module header"):
  # `module`, one blank line, the imports from line 3 on, one blank line, then
  # `@[expose] public section` and, one blank line under it, the module
  # docstring. A collector holds no declarations and so no section.
  seenFile[f] = 1
  if (isModule) {
    seenModule[f] = 1
    if (line2 != "")
      say(f ":2: `module` is followed by one blank line, then the imports")
    if (firstImpFNR > 0 && firstImpFNR != 3)
      say(f ":" firstImpFNR ": the imports start on line 3, one blank line under `module`")
    want = (lastImpFNR > 0) ? lastImpFNR + 2 : 3
    if (collector) {
      if (exposeCount > 0)
        say(f ":" exposeFNR ": a collector holds nothing but imports — no" \
            " `@[expose] public section`")
    } else if (exposeCount == 0) {
      say(f ":1: a module opens with `@[expose] public section`, one blank line under" \
          " the imports")
    } else {
      if (exposeCount > 1)
        say(f ":" exposeFNR ": more than one `@[expose] public section`")
      if (exposeFNR != want)
        say(f ":" exposeFNR ": `@[expose] public section` goes on line " want \
            ", one blank line under the last import")
      if (docLine > 0 && docLine != exposeFNR + 2)
        say(f ":" docLine ": the module docstring goes one blank line under" \
            " `@[expose] public section`, on line " exposeFNR + 2)
    }
  } else {
    if (exposeCount > 0)
      say(f ":" exposeFNR ": `@[expose] public section` in a file that is not a `module`")
    if (f !~ /^src\/CORALean\/Examples\// && !(f in nonmodOK))
      say(f ":1: not a module — a file opens with `module` (CONTRIBUTING, \"The module" \
          " header\"); only `Examples/` and the files in " NONMOD " stay non-module")
  }

  # Every `[N]` cited is defined and every one defined is cited, so a reference
  # cannot rot into a number with nothing behind it.
  for (i in refCite)
    if (!(i in refDef))
      say(f ":" refCite[i] ": cites `[" i "]`, which no `## References` entry defines")
  n = 0
  for (i in refDef) {
    n++
    if (!(i in refCite))
      say(f ":" refDef[i] ": defines `[" i "]` and never cites it")
  }
  for (i = 1; i <= n; i++)
    if (!(i in refDef))
      say(f ":" docLine ": references are numbered from 1 without gaps; `[" i "]` is missing")

  # One public declaration per file under `Operations/` or `Theorems/`
  # (`API.lean` excepted): the mechanism that keeps `aux_` from drifting into
  # a name promoted for reuse without earning its own file (issue #62). It holds in
  # `Complexity/Time/` and `Complexity/Space/` as everywhere: a cost is a file of
  # `Operations/`, its monotonicity and its O corollary are files of `Theorems/` (issue #187).
  # A `Basic.lean` holds one declaration per section instead, which
  # `check-basic-bundles.py` checks.
  # The `Operations/` of a conversion layer is the exception: the unit is the ordered pair, and
  # what one pair builds (`ellipsoid`, `ellipsoidNorm`, `ellipsoidBox`) is a file, named
  # `<Source>_to_<Target>`, however many definitions that is. A pair that builds one small thing is
  # a section of `Basic.lean` like anywhere else; its theorems are one to a file in `Theorems/`.
  if (f ~ /\/(Operations|Theorems)\// && !(f ~ /\/(API|Basic)\.lean$/) &&
      f !~ /\/Conversion\/(Real|Float)\/Operations\// && npub > MAX_PUBLIC_DECL) {
    decls = pubList[1]
    for (i = 2; i <= npub; i++) decls = decls ", " pubList[i]
    say(f ":1: " npub " public declarations, over " MAX_PUBLIC_DECL \
        " — rename file-local ones `aux_...`, or split into one file each: " decls)
  }

  dir = dirOf(f)
  want = moduleOf(dir "/API.lean")
  # A collector and a lakefile root may import collectors; no other file does.
  nroot = split(LAKE_ROOTS, rootList, " ")
  isRoot = 0
  for (i = 1; i <= nroot; i++) if (moduleOf(f) == rootList[i]) isRoot = 1
  for (i = 1; i <= nimp; i++) {
    if (!collector && !isRoot && imp[i] ~ /(^|\.)API$/)
      say(f ":" impLine[i] ": imports the collector " imp[i] \
          "; import the exact modules (CONTRIBUTING, API.lean)")
    if (imp[i] == want)
      say(f ":" impLine[i] ": imports the `API.lean` of its own directory, which is a cycle")
    # Only the two layers of a representation are kept apart so: a `Theorems/Real/` statement
    # elsewhere is about an operation written once over the scalar, which imports both.
    if (f ~ /\/ContSet\/.*\/Real\// && imp[i] ~ /\.Float\./)
      say(f ":" impLine[i] ": a `Real` file must not import `Float`")
    # The false axioms of the unsound baseline stay inside the bench: `NEAREST_AXIOM_FILE`.
    if (imp[i] ~ /(^|\.)NearestUnsound(\.|$)/ && index(f, BENCH_DIR) != 1)
      say(f ":" impLine[i] ": imports `" imp[i] "`, whose axioms are false — only" \
          " files under " BENCH_DIR " may")
  }

  if (f ~ /\/Conversion\/(Real|Float)\/Operations\// && !(f ~ /\/(API|Basic)\.lean$/) &&
      !(f ~ /\/[A-Za-z]+_to_[A-Za-z]+\.lean$/))
    say(f ":1: a file in `Conversion/*/Operations/` is named `<Source>_to_<Target>.lean`")

  # A layer directory and the namespace it declares must agree, since the path
  # is what a reader navigates by and the namespace is what Lean resolves by.
  # Only a representation has layers: a `Theorems/Real/` folder elsewhere holds
  # statements about the one scalar-generic object at `ℝ`, in the namespace of that object.
  if (!collector && nsLine > 0) {
    if (f ~ /\/Float\// && ns !~ /(^|\.)Float(\.|$)/)
      say(f ":" nsLine ": a file under `Float/` declares `namespace ...Float`, not `" ns "`")
    if (f ~ /\/ContSet\/.*\/Real\// && f !~ /\/Float\// && ns !~ /(^|\.)Real(\.|$)/)
      say(f ":" nsLine ": a file under `Real/` declares `namespace ...Real`, not `" ns "`")
  }

  # Section markers: `BEGIN CODE`/`END OF CODE` frame a file with declarations,
  # `AUXILIARY` marks the first `aux_` one, and a `MAIN ...`/`INSTANCES` marker
  # signposts the declaration a reader is looking for, which Lean always buries
  # last. `API.lean` and a file with no declarations at all carry none.
  isAPI = (f ~ /\/API\.lean$/)
  hasDecl = (nDeclTotal > 0)

  if (isAPI) {
    if (beginCount + endCount + auxCount + mainishCount > 0)
      say(f ":1: `API.lean` carries no section markers")
  } else if (!hasDecl) {
    if (beginCount + endCount + auxCount + mainishCount > 0)
      say(f ":1: a file with no declarations carries no section markers")
  } else {
    if (beginCount == 0)
      say(f ":1: missing the `BEGIN CODE` marker, after the author block and" \
          " before `namespace`")
    else if (beginCount > 1)
      say(f ":" beginFNR ": more than one `BEGIN CODE` marker")
    if (endCount == 0)
      say(f ":1: missing the `END OF CODE` marker, as the last line of the file")
    else if (endCount > 1)
      say(f ":" endFNR ": more than one `END OF CODE` marker")
    if (mainishCount == 0 && !isBasic)
      say(f ":1: missing the `MAIN ...` marker before the main declaration of the file")
    else if (mainishCount > 0 && isBasic)
      say(f ":" pendingMainFNR ": a `Basic.lean` carries no `MAIN ...` marker — each" \
          " section banner names its declaration")
    else if (mainishCount > 1)
      say(f ":" pendingMainFNR ": more than one `MAIN ...`/`INSTANCES` marker")

    if (beginFNR > 0 && nsLine > 0 && beginFNR > nsLine)
      say(f ":" beginFNR ": `BEGIN CODE` must come before `namespace`")
    if (beginFNR > 0 && authorLine > 0 && beginFNR < authorLine && !isBasic)
      say(f ":" beginFNR ": `BEGIN CODE` must come after the author block")
    if (endFNR > 0 && endFNR != lastFNR)
      say(f ":" endFNR ": `END OF CODE` must be the last line of the file")

    n = 0
    for (a in declAux) n++
    if (n > 0 && auxCount == 0)
      say(f ":1: file has `aux_` declarations but no `AUXILIARY` marker")
    if (n == 0 && auxCount > 0)
      say(f ":1: `AUXILIARY` marker present but the file has no `aux_` declaration")
  }

  if (pendingMain)
    say(f ":" pendingMainFNR ": `" pendingMainLabel "` marker is not followed by a declaration")
  if (afterPending)
    say(f ":" afterMarkerFNR ": `" afterLabel "` marker is not followed by a blank line" \
        " and then content")
}

FNR == 1 {
  if (prev != "") check(prev)
  prev = FILENAME
  depth = 0; nimp = 0; docLine = 0; docLen = 0; docEnd = 0
  authorLine = 0; blockEnd = 0; revDash = 0; codeLine = 0; nsLine = 0; ns = ""
  blockKind = ""; blockStart = 0; declDocEnd = 0
  prevPureComment = 0; prevLineComment = 0; run = 0; blanks = 0; inRefs = 0; refsLine = 0
  firstDeclSeen = 0; firstBodyFound = 0; firstBodyLine = 0
  npub = 0; nDeclTotal = 0; lastFNR = 0; defPending = 0; nh1 = 0; cexWord = 0; cexNeg = 0; cexDecl = ""; sigOpen = 0
  beginCount = 0; endCount = 0; auxCount = 0; mainishCount = 0
  inStruct = 0; split("", sField)
  beginFNR = 0; endFNR = 0
  afterPending = 0; afterLabel = ""; afterMarkerFNR = 0; afterBlanks = 0
  pendingMain = 0; pendingMainLabel = ""; pendingMainFNR = 0; pendingMainIsInstances = 0
  isModule = ($0 == "module"); line2 = ""; firstImpFNR = 0; lastImpFNR = 0
  isBasic = (FILENAME ~ /\/Basic\.lean$/)
  exposeCount = 0; exposeFNR = 0
  # `split("", a)` rather than `delete a`, which older mawk does not have
  split("", declAux); split("", useAux); split("", imp); split("", impLine)
  split("", refDef); split("", refCite); split("", pubList)
}

{
  raw = $0
  lastFNR = FNR
  priorBlanks = blanks
  isMarkerLine = (raw in markerLabel)

  # Resolve the marker seen on an earlier line: normally the gap to whatever
  # comes next must be exactly one blank line, but two adjacent markers with
  # nothing between them (a file with no `namespace`, and one declaration
  # right where `BEGIN CODE` also anchors) share a gap, which must then be the
  # two blank lines the second marker requires before it rather than one.
  if (afterPending && raw ~ /[^ \t]/) {
    wantAfter = isMarkerLine ? 2 : 1
    if (afterBlanks != wantAfter)
      say(FILENAME ":" afterMarkerFNR ": `" afterLabel "` marker has " afterBlanks \
          " blank line(s) after it, not " wantAfter)
    afterPending = 0
  } else if (afterPending) {
    afterBlanks++
  }

  if (isMarkerLine) {
    label = markerLabel[raw]
    if (priorBlanks != 2)
      say(FILENAME ":" FNR ": `" label "` marker has " priorBlanks \
          " blank line(s) before it, not 2")
    if (label == "BEGIN CODE") {
      beginCount++; beginFNR = FNR
    } else if (label == "END OF CODE") {
      endCount++; endFNR = FNR
    } else if (label == "AUXILIARY") {
      auxCount++
      afterPending = 1; afterLabel = label; afterMarkerFNR = FNR; afterBlanks = 0
    } else {
      mainishCount++
      if (label == "INSTANCES" && FILENAME !~ /\/Instances\.lean$/)
        say(FILENAME ":" FNR ": the `INSTANCES` label is only for `Instances.lean`")
      if (label != "INSTANCES" && FILENAME ~ /\/Instances\.lean$/)
        say(FILENAME ":" FNR ": `Instances.lean` holds several anonymous instances" \
            " with no single main one — use the `INSTANCES` label")
      pendingMain = 1; pendingMainLabel = label; pendingMainFNR = FNR
      pendingMainIsInstances = (label == "INSTANCES")
      afterPending = 1; afterLabel = label; afterMarkerFNR = FNR; afterBlanks = 0
    }
  } else if (isBasic && raw ~ SECTION_BANNER) {
    # A section of a `Basic.lean` opens with its banner and its own author block,
    # which the field checks below then read like the block of a file. The exact
    # banner, and the rest of what a section is, `check-basic-bundles.py` checks.
    if (priorBlanks != 2)
      say(FILENAME ":" FNR ": a section banner has " priorBlanks \
          " blank line(s) before it, not 2")
    authorLine = 0; revDash = 0; blockEnd = 0
    endRun(FILENAME)
  } else if (raw ~ /^-- [-=]/) {
    say(FILENAME ":" FNR ": looks like a section marker but does not match the" \
        " canonical form — check the width and the fill either side of the label")
  }

  # No asserted cost is `0` (CONTRIBUTING, "Complexity"): the result of an operation is written
  # scalar by scalar, so a `def ... : Cost := 0` under `Complexity/Time/` needs a reason in the
  # zero-cost list. The body may sit on the next line.
  if (FILENAME ~ /\/Complexity\/Time\// && raw !~ /^[ \t]*--/) {
    zname = ""
    if (raw ~ /^(noncomputable )?def [^ ]+.*Cost :=[ \t]*(0|⟨0⟩)[ \t]*$/) zname = raw
    else if (zheadFNR > 0 && FNR == zheadFNR + 1 && raw ~ /^[ \t]+(0|⟨0⟩)[ \t]*$/) zname = zhead
    zheadFNR = 0
    if (raw ~ /^(noncomputable )?def [^ ]+.*Cost :=[ \t]*$/) { zhead = raw; zheadFNR = FNR }
    if (zname != "") {
      sub(/^(noncomputable )?def /, "", zname); sub(/[ \t([{:].*$/, "", zname)
      if (zname in zeroOK) zeroUsed[zname] = 1
      else say(FILENAME ":" FNR ": `" zname "` is a cost of `0`, but an operation that builds" \
               " a result writes it; count the writes, or list the name in " ZEROLIST \
               " with the reason it writes nothing")
    }
  }

  # An import cannot be wrapped, so the `public `/`meta ` a module adds to one
  # is not counted: `import <name>` alone must fit, as it did before.
  lenLine = raw
  if (raw ~ IMPORT) sub(/^(public[ \t]+)?(meta[ \t]+)?/, "", lenLine)
  if (charlen(lenLine) > MAX_LINE)
    say(FILENAME ":" FNR ": line is " charlen(lenLine) " characters, over the limit of " \
        MAX_LINE " — wrap it")
  if (!cexWord && raw ~ /[Cc]ounterexample|Cora([^a-z]|$)/) cexWord = 1
  if (FNR == 2) line2 = raw
  if (raw ~ /[ \t]$/)
    say(FILENAME ":" FNR ": trailing whitespace — strip it")
  if (raw ~ /\t/)
    say(FILENAME ":" FNR ": tab character — indent with spaces")
  if (raw !~ /[^ \t]/) { blanks++; if (blanks == 3) say(FILENAME ":" FNR \
      ": third blank line in a row — one blank line separates, two at most") }
  else blanks = 0
  if (authorLine == 0 && raw ~ /^-- Authors:/) { authorLine = FNR; blockEnd = FNR + 3 }

  # The author block, field by field, so that a block that is present but
  # malformed is caught rather than counted as present.
  # `Reviewed:` may continue on further lines, aligned to the value column.
  if (authorLine > 0 && FNR == blockEnd + 1 && raw ~ /^--[ ]+[0-9][0-9]-[A-Za-z]/) {
    blockEnd = FNR
    if (revDash)
      say(FILENAME ":" FNR ": `Reviewed: ---` stands alone — a review replaces it")
    else if (substr(raw, 1, 18) != "--" sprintf("%16s", "") || substr(raw, 19) !~ /^[0-9]/)
      say(FILENAME ":" FNR ": a `Reviewed:` continuation line is `--` and spaces up to" \
          " the column the dates start in")
    else {
      val = substr(raw, 19); sub(/[ \t]+$/, "", val)
      checkReview(val, FNR)
    }
  }
  if (authorLine > 0 && FNR >= authorLine && FNR <= authorLine + 3) {
    field = ""
    if (FNR == authorLine) field = "Authors:      "
    else if (FNR == authorLine + 1) field = "Written:      "
    else if (FNR == authorLine + 2) field = "Last update:  "
    else field = "Reviewed:     "
    lbl = field; sub(/[ \t]*$/, "", lbl)
    if (index(raw, "-- " field " ") != 1) {
      say(FILENAME ":" FNR ": the author block reads `-- " lbl \
          "` here, aligned to one column")
    } else {
      val = substr(raw, length("-- " field " ") + 1)
      sub(/[ \t]+$/, "", val)
      if (FNR == authorLine) {
        n = split(val, who, /, */)
        for (k = 1; k <= n; k++)
          if (who[k] !~ /^Claude (Opus|Sonnet|Fable|Haiku) [0-9]+(\.[0-9]+)?$/)
            say(FILENAME ":" FNR ": `Authors:` lists the models that wrote the file," \
                " comma-separated, each `Claude <Opus|Sonnet|Fable|Haiku> <version>`," \
                " not `" who[k] "`")
      } else if (FNR == authorLine + 1) {
        if (val !~ DATE)
          say(FILENAME ":" FNR ": `Written:` is a DD-Month-YYYY date, not `" val "`")
      } else if (FNR == authorLine + 2) {
        if (val != "---" && val !~ DATE)
          say(FILENAME ":" FNR ": `" lbl "` is a DD-Month-YYYY date or `---`, not `" val "`")
      } else if (val == "---") {
        revDash = 1
      } else {
        checkReview(val, FNR)
      }
    }
  }
  isAuthorBlock = (authorLine > 0 && FNR >= authorLine && FNR <= blockEnd)

  depthBefore = depth
  code = strip(raw)
  # No binder is called `temp` or `tmp` or a variant (#191): name the value for what it is.
  noStr = code; gsub(/"([^"\\]|\\.)*"/, "\"\"", noStr)
  if ((bad = tmpName(noStr)) != "")
    say(FILENAME ":" FNR ": a binder called `" bad "` — name it for what it holds")

  if (depthBefore == 0 && opened != "") { blockKind = opened; blockStart = FNR }
  lineKind = blockKind
  if (depth == 0 && blockKind != "") closeBlock(FNR)

  # References live in the module docstring; everything else that names a
  # number in brackets is citing one.
  if (lineKind == "mod") {
    if (raw ~ /^# /) nh1++
    if (raw ~ /^#+ References[ \t]*$/) { inRefs = 1; if (refsLine == 0) refsLine = FNR }
    else if (raw ~ /^#+ /) inRefs = 0
    if (inRefs && raw ~ /^\* \[[0-9]+\] /) {
      num = raw; sub(/^\* \[/, "", num); sub(/\].*$/, "", num)
      if (num in refDef)
        say(FILENAME ":" FNR ": `[" num "]` is defined twice")
      refDef[num + 0] = FNR
      next
    }
  }
  # A citation is `[N]` or `[N, Sec. 4]` with N counting from 1. The exclusions
  # are what a tree full of interval and matrix notation forces: `[0, 1]` and
  # `[1/3, 1]` are sets, `[[1],[3]]` is a matrix, and `[1, 2]` is a pair.
  if (sawComment || lineKind != "") {
    rest = raw
    while (match(rest, /\[[1-9][0-9]*(\]|, *[^0-9 ])/)) {
      num = substr(rest, RSTART + 1, RLENGTH - 2)
      sub(/[],].*$/, "", num)
      after = substr(rest, RSTART + RLENGTH - 1, 2)
      if (!(RSTART > 1 && substr(rest, RSTART - 1, 1) == "[") && after != "]]" &&
          !(num in refCite))
        refCite[num + 0] = FNR
      rest = substr(rest, RSTART + RLENGTH)
    }
  }

  # One line of `--` says the non-obvious thing; two say a paragraph, which
  # belongs in the module docstring.
  isPureComment = (code !~ /[^ \t]/) && (raw ~ /^[ \t]*--/) && !isAuthorBlock
  if (isPureComment && prevPureComment)
    say(FILENAME ":" FNR ": second `--` line in a row — one line, or move it to the header")
  prevPureComment = isPureComment

  # Where the first declaration body begins: a hypothesis list is a signature,
  # not a proof step, so the density rule below opens only once one is reached.
  if (!firstBodyFound) {
    if (!firstDeclSeen && code ~ DECL_START) firstDeclSeen = 1
    if (firstDeclSeen && (code ~ /:=/ || code ~ /(^|[ \t])where([ \t]|$)/)) {
      firstBodyLine = FNR; firstBodyFound = 1
    }
  }

  # A minimum density. Counted only past the header and the first declaration
  # signature, and only over lines that carry code, so blank lines neither help
  # nor hurt. Reported once per stretch, at the line the stretch began, since
  # that is where the comment goes.
  # In a `Counterexamples/` file every declaration has its signature exempt, not only the first:
  # the model comes first and the long statement of the refutation after it.
  if (FILENAME ~ /\/Counterexamples\// && code ~ DECL_START) sigOpen = 1
  inSig = sigOpen
  if (sigOpen && (code ~ /:=/ || code ~ /(^|[ \t])where([ \t]|$)/)) sigOpen = 0
  if (authorLine > 0 && FNR > blockEnd && firstBodyFound && FNR > firstBodyLine) {
    if (sawComment || lineKind != "") {
      endRun(FILENAME)
    } else if (code ~ /[^ \t]/ && !inSig) {
      if (run == 0) runStart = FNR
      run++
    }
  }

  if (code ~ IMPORT) {
    nimp++
    imp[nimp] = code
    sub(IMPORT, "", imp[nimp])
    sub(/[ \t]+$/, "", imp[nimp])
    impLine[nimp] = FNR
    if (firstImpFNR == 0) firstImpFNR = FNR
    lastImpFNR = FNR
    if (!isModule && code ~ /^(public|meta)[ \t]/)
      say(FILENAME ":" FNR ": `public`/`meta` import in a file that is not a `module`")
  } else if (code == "module") {
    if (FNR != 1)
      say(FILENAME ":" FNR ": `module` is the first line of a file, or absent")
  } else if (raw == "@[expose] public section") {
    exposeCount++
    if (exposeFNR == 0) exposeFNR = FNR
  } else if (code ~ /public[ \t]+section/) {
    say(FILENAME ":" FNR ": the section of a module is `@[expose] public section`, exactly")
  } else if (code ~ /[^ \t]/) {
    if (codeLine == 0) codeLine = FNR
  }

  if (nsLine == 0 && code ~ /^namespace /) {
    ns = code; sub(/^namespace[ \t]+/, "", ns); sub(/[ \t].*$/, "", ns)
    nsLine = FNR
  }

  if (code ~ /(^|[^A-Za-z0-9_'"'"'.])sorry([^A-Za-z0-9_'"'"']|$)/)
    say(FILENAME ":" FNR ": `sorry` — finish the proof or drop the declaration")
  # A pair of one scalar twice: the bounds of one quantity belong in an `Interval`.
  if (FILENAME !~ /^src\/CORALean\/Examples\// &&
      (index(code, "ℝ × ℝ") || index(code, "𝕋 × 𝕋") || index(code, "α × α") ||
       index(code, "EReal × EReal"))) {
    pairSeen[FILENAME] = 1
    if (!(FILENAME in pairOK) && !(FILENAME in pairWarned)) {
      pairWarned[FILENAME] = 1
      say(FILENAME ":" FNR ": a pair `ℝ × ℝ`/`𝕋 × 𝕋`/`α × α`/`EReal × EReal` — bounds of one quantity are an" \
          " `Interval`; if this pair is two quantities, list the file in " PAIRLIST " with the reason")
    }
  }
  # Sibling fields that are the two bounds of one quantity (`remInf`/`remSup`, `tLo`/`tHi`,
  # `loX`/`hiX`): the same rule as the pair above, spelt as two fields. Listed files carry the
  # same entry in PAIR_LIST.
  if (FILENAME !~ /^src\/CORALean\/Examples\// && code ~ /^(structure|class)[ \t]/ &&
      code !~ /^class[ \t]+inductive/) {
    inStruct = 1; split("", sField)
  } else if (inStruct && code ~ /^[^ \t]/) {
    inStruct = 0
  } else if (inStruct && code ~ /^  [A-Za-z_][^:=()\[\]{}]*:/ && code !~ /^  [A-Za-z_][^:]*:=/) {
    fl = code; sub(/^[ \t]+/, "", fl); sub(/[ \t]*:.*$/, "", fl)
    nfl = split(fl, fnames, /[ \t]+/)
    for (fi = 1; fi <= nfl; fi++) {
      fn = fnames[fi]; sField[fn] = 1; fp = ""
      if (fn ~ /^.+Inf$/) fp = substr(fn, 1, length(fn) - 3) "Sup"
      else if (fn ~ /^.+Sup$/) fp = substr(fn, 1, length(fn) - 3) "Inf"
      else if (fn ~ /^.+Lo$/) fp = substr(fn, 1, length(fn) - 2) "Hi"
      else if (fn ~ /^.+Hi$/) fp = substr(fn, 1, length(fn) - 2) "Lo"
      else if (fn ~ /^lo($|[A-Z])/) fp = "hi" substr(fn, 3)
      else if (fn ~ /^hi($|[A-Z])/) fp = "lo" substr(fn, 3)
      if (fp != "" && (fp in sField)) {
        pairSeen[FILENAME] = 1
        if (!(FILENAME in pairOK) && !(FILENAME in pairWarned)) {
          pairWarned[FILENAME] = 1
          say(FILENAME ":" FNR ": the fields `" fn "` and `" fp "` are the two bounds of one quantity —" \
              " hold them as one `Interval` field; if they are two quantities, list the file in " \
              PAIRLIST " with the reason")
        }
      }
    }
  }
  # A guarantee about an `Option` result is stated at `… = some R` (CONTRIBUTING,
  # "Verification"): a `match` arm `| none => True` closing a statement is a
  # proof about a run that returned nothing, which reads as a passed check.
  if (code ~ /^[ \t]*\|[ \t]*none[ \t]*=>[ \t]*True[ \t]*(:=.*)?$/)
    say(FILENAME ":" FNR ": `| none => True` — state the guarantee at `… = some R`," \
        " so a failed run has nothing to enclose rather than a `True`")
  if (code ~ /^axiom[ \t]/ && FILENAME == NEAREST_AXIOM_FILE) {
    if (code !~ ("^axiom[ \t]+" NEAREST_AXIOM "([ \t:]|$)"))
      say(FILENAME ":" FNR ": `axiom` — this file assumes `" NEAREST_AXIOM "` and" \
          " nothing else, so one name in `#print axioms` flags the false baseline")
  } else if (code ~ /^axiom[ \t]/ && FILENAME == FLINT_AXIOM_FILE) {
    if (code !~ ("^axiom[ \t]+" FLINT_AXIOM "([ \t:]|$)"))
      say(FILENAME ":" FNR ": `axiom` — this file assumes `" FLINT_AXIOM "` and" \
          " nothing else, so one name in `#print axioms` flags the FLINT backend")
  } else if (code ~ /^axiom[ \t]/ && FILENAME != AXIOM_FILE)
    say(FILENAME ":" FNR ": `axiom` — only " AXIOM_FILE " axiomatises anything" \
        " (and " NEAREST_AXIOM_FILE ", the unsound bench baseline, and " \
        FLINT_AXIOM_FILE ", the optional FLINT backend)")
  # Banned outright rather than tracked per-section: nothing in the tree uses
  # it today, and tracking which declarations a `section` covers would mean a
  # second, stateful way to be `noncomputable` beside marking a declaration
  # itself — one form is simpler than two and keeps every check below exact.
  if (code ~ /^noncomputable section([ \t]|$)/)
    say(FILENAME ":" FNR ": `noncomputable section` — mark each declaration" \
        " `noncomputable` individually, so this check can see it")

  # Search tactics cost compile time that nothing bounds, and the whole point of
  # the heartbeat limit in `lakefile.toml` is that a proof does not start
  # searching. Matched in tactic position only: `decide` is also the term that
  # turns a `Decidable` instance into a `Bool`, which is not a search at all.
  tac = code
  sub(/^[ \t]+/, "", tac)
  SEARCH = "(aesop|exact\\?|apply\\?|simp\\?|rw\\?|decide|native_decide|polyrith|library_search)"
  if (tac ~ ("^" SEARCH "([ \t;<]|$)") ||
      tac ~ ("(by|<;>|;|·|\\|) *" SEARCH "([ \t;<]|$)")) {
    match(tac, SEARCH)
    say(FILENAME ":" FNR ": `" substr(tac, RSTART, RLENGTH) \
        "` — proofs here are explicit, so the heartbeat limit stays meaningful")
  }

  # A heartbeat bump is a cost someone chose to pay; the reason is the only part
  # a later reader cannot reconstruct.
  if (code ~ /^set_option maxHeartbeats /) {
    if (!(sawComment && raw ~ /--/) && !(prevLineComment))
      say(FILENAME ":" FNR ": a `maxHeartbeats` bump carries a one-line reason," \
          " above it or after it on this line")
  }
  # `set_option ... in` between a docstring and its declaration silently
  # detaches the docstring from it.
  if (code ~ /^set_option .* in[ \t]*$/ && declDocEnd == FNR - 1)
    say(FILENAME ":" FNR ": `set_option ... in` goes above the docstring, not between" \
        " it and the declaration")
  prevLineComment = (code !~ /[^ \t]/) && sawComment

  if (code ~ DECL_START) {
    match(code, DECL_START)
    prefix = substr(code, RSTART, RLENGTH)
    match(prefix, KIND)
    kind = substr(prefix, RSTART, RLENGTH)
    decl = code
    sub(DECL_PREFIX, "", decl)
    sub(/[^A-Za-z0-9_'"'"'.].*$/, "", decl)
    b = base(decl)
    # The declaration name as written, for the `noncomputable` allowlist:
    # unlike `decl`/`b`, kept whole rather than trimmed to identifier
    # characters, so a dotted prefix (`LinearSys.reach`) and a non-ASCII byte
    # (`norm₂`, a UTF-8 continuation byte under `LC_ALL=C`) both survive, and
    # two representations own same-named operations stay two distinct entries.
    # Cut only at what can never appear inside an identifier: whitespace, or
    # the start of a binder or a type ascription.
    qualDecl = code
    sub(DECL_PREFIX, "", qualDecl)
    sub(/[ \t([{:].*$/, "", qualDecl)
    nDeclTotal++
    if (!cexNeg && qualDecl ~ /(^|[._])not_|_not([_.]|$)|_ne([_.]|$)|(^|_)ne_|[Cc]ora/) cexNeg = 1

    # A public definition named for the CORA code (`…Cora`) or a theorem named `…counterexample`
    # belongs in a `Counterexamples/` folder (#148); `check` reports the first one found.
    if (cexDecl == "" && b !~ /^aux_/ && prefix !~ /private /) {
      if ((kind == "theorem" || kind == "lemma") ? (b ~ /[Cc]ounterexample$/) \
          : (b ~ /[Cc]ora([A-Z0-9_]|$)/))
        cexDecl = FNR ":" qualDecl
    }

    # Whatever `MAIN ...`/`INSTANCES` marker is still open closes on the first
    # declaration seen after it, regardless of how many comment or blank lines
    # sit in between.
    if (pendingMain) {
      if (!pendingMainIsInstances) {
        want = mainLabelForKind[kind]
        if (want != pendingMainLabel)
          say(FILENAME ":" pendingMainFNR ": `" pendingMainLabel "` marker precedes a `" \
              kind "` declaration at line " FNR ", which needs `" want "`")
      }
      pendingMain = 0
    }

    # A `Complexity/Time/` directory holds asserted running costs and nothing derived from
    # a definition; the `...Cost` name is one of the three things that says so,
    # the directory and the `Cost`-valued `def` being the other two.
    if (FILENAME ~ /\/Complexity\/Time\// && kind == "def" && b !~ /^aux_/ && b !~ /(Cost|Bound)$/)
      say(FILENAME ":" FNR ": a `def` under `Complexity/Time/` is an asserted cost, named" \
          " `...Cost` or `...Bound`, not `" b "`")

    # Rule C (#149). A `Theorems/` file states and proves a guarantee; what it is a guarantee
    # *about* is declared elsewhere. A `def`, `abbrev`, `instance`, `structure`, `class`,
    # `inductive` or `opaque` there is a definition in the wrong file: it belongs in
    # `Definitions/` (a type, a proposition, a set, a specification) or `Operations/` (an
    # algorithm). Free are the declarations that serve one proof only — `private` and `aux_`.
    if (FILENAME ~ /\/Theorems\// &&
        FILENAME !~ /\/API\.lean$/ && kind != "theorem" && kind != "lemma" &&
        prefix !~ /private / && b !~ /^aux_/)
      say(FILENAME ":" FNR ": a `" kind "` in a theorem file — `" qualDecl "` is a definition," \
          " which belongs in `Definitions/` (a type, proposition, set or specification) or" \
          " `Operations/` (an algorithm); only `private` and `aux_` helpers of one proof stay")

    # `noncomputable` is free in the `Real/` layer of a representation (rule 1),
    # in the instance of the scalar interface at ℝ, `Global/Float/Instances/Real/`
    # (rule 2), and in a `Definitions/` file, which says what an object means
    # and is never run, and in a `Counterexamples/` file, whose models are read, not run.
    # Elsewhere it is free only for an `aux_` declaration
    # (rule 3) or a name the allowlist gives a reason (rule 4), and under
    # `Float/` even the allowlist does not reach: the float layer exists to run.
    if (prefix ~ /noncomputable /) {
      isAux = (b ~ /^aux_/)
      if (FILENAME !~ /\/ContSet\/.*\/Real\// && FILENAME !~ /\/Global\/Float\/Instances\/Real\// &&
          FILENAME !~ /\/Definitions\// && FILENAME !~ /\/Counterexamples\//) {
        if (FILENAME ~ /\/Float\//) {
          if (!isAux)
            say(FILENAME ":" FNR ": `noncomputable` under `Float/` — only an" \
                " `aux_` declaration may be; the float layer must run")
        } else if (isAux) {
          # exempt
        } else if (qualDecl in allowNC) {
          usedAllow[qualDecl] = 1
        } else {
          say(FILENAME ":" FNR ": `noncomputable` outside a `Real/` layer or" \
              " `Definitions/`, not an `aux_` declaration, and `" qualDecl "` is not in `" \
              ALLOWLIST "` — add it there with a reason, or make the" \
              " declaration computable")
        }
      }
    }

    # Rule B. A `Definitions/` file holds meanings: types, propositions, sets,
    # and what is `noncomputable` because it is a specification. A theorem
    # there belongs in `Theorems/`, and a computable `def` returning data is
    # an algorithm, which belongs in `Operations/`; its header is read up to
    # `:=` below, since the result type may sit lines after the name.
    if (FILENAME ~ /\/Definitions\// && FILENAME !~ /\/API\.lean$/) {
      if (kind == "theorem" || kind == "lemma")
        say(FILENAME ":" FNR ": a theorem in `Definitions/` — `" qualDecl \
            "` belongs in `Theorems/`")
      else if ((kind == "def" || kind == "instance") && prefix !~ /noncomputable /) {
        defPending = 1; defFNR = FNR; defHdr = ""; defName = qualDecl; defNC = 0
      }
      # `noncomputable` does not make a partial algorithm a meaning: a `def`
      # returning `Option …` searches or can fail, which is an Operation.
      else if (kind == "def" && prefix ~ /noncomputable /) {
        defPending = 1; defFNR = FNR; defHdr = ""; defName = qualDecl; defNC = 1
      }
    }

    if (b ~ /^aux_/) {
      declAux[b] = FNR
      # An instance is found by type class search, never by name, so no file
      # can ever establish that nothing outside it uses one — `aux_` asserts
      # exactly that, and would be a standing false statement on an instance.
      if (prefix ~ /instance $/)
        say(FILENAME ":" FNR ": `aux_` on an instance is never justified — " \
            "`" b "` is found by type class search from any file, not by this name")
    }
    # One public declaration per `Operations/`/`Theorems/` file (#62): a
    # `private` declaration and an `aux_`-named one are file-local by
    # convention and do not count against the limit.
    else if (prefix !~ /private /) { npub++; pubList[npub] = b }
  }

  if (defPending) {
    defHdr = defHdr " " code
    if (defHdr ~ /:=/ || defHdr ~ / where([ \t]|$)/ || (FNR > defFNR && code ~ /^[ \t]*\|/)) {
      defPending = 0
      if (defNC && returnsOption(defHdr))
        say(FILENAME ":" defFNR ": `" defName "` returns an `Option`, a search that" \
            " can fail, which is an Operation — move it to `Operations/`")
      else if (!defNC && !propOrSet(defHdr))
        say(FILENAME ":" defFNR ": `" defName "` is a computable `def` returning data," \
            " which is an Operation — move it to `Operations/`, or it is a `Prop`/`Set`" \
            " and should say so in its type")
    }
  }

  rest = code
  while (match(rest, /aux_[A-Za-z0-9_'"'"']*/)) {
    tok = substr(rest, RSTART, RLENGTH)
    if (!(tok in useAux)) useAux[tok] = FNR
    rest = substr(rest, RSTART + RLENGTH)
  }
}

END {
  if (prev != "") check(prev)
  # The stale-entry reports need the declarations of every file, which a staged run lacks.
  if (!STALE) exit
  for (name in allowNC)
    if (!(name in usedAllow))
      say(ALLOWLIST ":" allowLine[name] ": stale allowlist entry `" name \
          "` — no longer matches any `noncomputable` declaration the rules do not already allow")
  for (zn in zeroOK)
    if (!(zn in zeroUsed))
      say(ZEROLIST ":" zeroLine[zn] ": stale entry `" zn "` — no longer a `Cost` of `0` under" \
          " `Complexity/Time/`; the list only shrinks")
  for (p in cexOK)
    if (!(p in cexUsed))
      say("scripts/check-conventions.sh: stale COUNTEREXAMPLE_EXCEPTIONS entry `" p \
          "` — the file is gone or no longer asks to live in `Counterexamples/`")
  for (p in pairOK)
    if (!(p in seenFile))
      say(PAIRLIST ":" pairLine[p] ": stale entry `" p "` — no such file")
    else if (!(p in pairSeen))
      say(PAIRLIST ":" pairLine[p] ": stale entry `" p "` — the file spells no such pair now;" \
          " the list only shrinks")
  for (p in nonmodOK) {
    if (p ~ /^src\/CORALean\/Examples\//)
      say(NONMOD ":" nonmodLine[p] ": `" p "` is under `Examples/`, which needs no entry")
    else if (!(p in seenFile))
      say(NONMOD ":" nonmodLine[p] ": stale entry `" p "` — no such file")
    else if (p in seenModule)
      say(NONMOD ":" nonmodLine[p] ": stale entry `" p "` — it is a module now; the list" \
          " only shrinks")
  }
}
')
report "$out"

if [ -z "$STAGED" ]; then

# Every module reachable from a root, so a file that was written but never
# collected is caught rather than silently left out of the build. The roots are
# the roots of the targets `lakefile.toml` names, and a new target belongs in
# both places. Reuses `$list`, built above for the same reason this pass needs
# it: it is global by nature, and a split would report every module it
# happened not to see an importer for.

out=$(awk -v LIST="$list" \
  -v ROOTS="CORALean CORALean.Global.Float.Instances.Flint.API CORALean.Examples.API \
    CORALean.Examples.Demo CORALean.Examples.Bench CORALean.Examples.BenchFlint \
    CORALean.Examples.BenchFlintMain CORALean.Examples.Oracle CORALean.Examples.HardwareCheck \
    CORALean.Examples.FlintCheck CORALean.Examples.RunCheck CORALean.Examples.Bench.OracleUnsound" '
BEGIN { while ((getline f < LIST) > 0) if (f != "") ARGV[ARGC++] = f }
function moduleOf(path,   m) {
  m = path; sub(/^src\//, "", m); sub(/\.lean$/, "", m); gsub("/", ".", m)
  return m
}
FNR == 1 { mod = moduleOf(FILENAME); known[mod] = 1; depth = 0 }
/^(public[ \t]+)?(meta[ \t]+)?import[ \t]/ {
  dep = $0; sub(/^(public[ \t]+)?(meta[ \t]+)?import[ \t]+/, "", dep); sub(/[ \t]+$/, "", dep)
  edge[mod] = edge[mod] " " dep
}
END {
  nroots = split(ROOTS, roots, " ")
  head = 1; tail = 0
  for (i = 1; i <= nroots; i++) { seen[roots[i]] = 1; queue[++tail] = roots[i] }
  while (head <= tail) {
    cur = queue[head]; head++
    n = split(edge[cur], deps, " ")
    for (i = 1; i <= n; i++)
      if (deps[i] != "" && !(deps[i] in seen)) { seen[deps[i]] = 1; queue[++tail] = deps[i] }
  }
  for (m in known)
    if (!(m in seen)) print m ": not reachable from a target root — nothing imports it"
}
' | sort)
report "$out"

# The layout, read off the file list alone: Rule A, and where a scalar folder
# may sit. The scalar is a folder only where the data of a type differs by
# layer, which is exactly the representations of `ContSet/`; everywhere else an
# object is written once over the scalar, `Theorems/Real/` holds what only ℝ
# can state of it, and `Global/Float/` is the scalar interface itself.
out=$(awk -v LIST="$list" \
  -v PENDING="$(printf '%s' "$CLASS_ROOT_PENDING" | tr '\n' ' ')" '
function dirOf(p,   d) { d = p; sub(/\/[^\/]*$/, "", d); return d }
function baseOf(p,   b) { b = p; sub(/^.*\//, "", b); return b }
BEGIN {
  n = split(PENDING, pl, " ")
  for (i = 1; i <= n; i++) if (pl[i] != "") pending[pl[i]] = 1
  while ((getline f < LIST) > 0) {
    if (f == "") continue
    d = dirOf(f); b = baseOf(f)
    # Complexity is laid out as everywhere else (issue #187): `Complexity/Time/Operations/` holds
    # the asserted costs, `Complexity/Time/Theorems/` what is proved of them (monotonicity, the
    # `O` corollary), and `Complexity/Space/Theorems/` the sizes, which are theorems and so have
    # no `Operations/`. Small declarations are sections of the `Basic.lean` of those directories.
    if (f ~ /\/Cost\//)
      print f ": a `Cost/` directory no longer exists; the cost of an operation is" \
            " a file of `Complexity/Time/Operations/`"
    if (f ~ /\/Complexity\/[^\/]*\.lean$/ && b != "API.lean")
      print f ": a file directly in `Complexity/` — only `API.lean` sits there; costs are in" \
            " `Complexity/Time/Operations/`, what is proved of them in `Complexity/Time/Theorems/`," \
            " sizes in `Complexity/Space/Theorems/`"
    if (f ~ /\/Complexity\/(Time|Space)\/[^\/]*\.lean$/ && b != "API.lean")
      print f ": a file directly in `Complexity/Time/` or `Complexity/Space/` — only `API.lean`" \
            " sits there; the files are in `Operations/` (Time only) and `Theorems/`"
    if (f ~ /\/Complexity\/Space\/Operations\//)
      print f ": `Complexity/Space/` has no `Operations/`: a size is a theorem about the result," \
            " in `Complexity/Space/Theorems/`"
    if (b != "API.lean" && b != "Instances.lean" && b != "Interfaces.lean") { nextra[d]++; extra[d] = extra[d] " `" b "`" }
    # A directory is a class root once any role folder sits directly in it.
    cur = d
    while (cur ~ /\//) {
      nm = baseOf(cur); par = dirOf(cur)
      if (nm == "Operations" || nm == "Theorems" || nm == "Definitions") root[par] = 1
      cur = par
    }
    if (f ~ /^src\/CORALean\/ContSet\//) continue
    t = f; gsub(/\/(Theorems|Counterexamples)\/Real\//, "/Theorems/-/", t)
    if (t ~ /\/Real\// && f !~ /^src\/CORALean\/Global\/Float\//)
      print f ": a `Real/` folder outside `ContSet/` is a `Theorems/Real/` only," \
            " for what holds of a scalar-generic object at ℝ alone"
    if (f ~ /\/Float\// && f !~ /^src\/CORALean\/Global\/Float\//)
      print f ": a `Float/` folder outside `ContSet/` is `Global/Float/` only, the scalar" \
            " interface; everything else is written once over the scalar"
  }
  for (d in root) {
    if (d in pending) continue
    if (nextra[d] > 1)
      print d ": a class root holds its class file, `Interfaces.lean`, `Instances.lean` and `API.lean` only," \
            " and this one holds " nextra[d] ":" extra[d] " — one is the class file, the" \
            " rest belong in `Definitions/`, `Operations/` or `Theorems/`"
  }
  for (d in pending)
    if (!(d in root) || nextra[d] <= 1)
      print "scripts/check-conventions.sh: `" d "` is on CLASS_ROOT_PENDING but" \
            " already has its role folders sorted — drop it from the list"
}
' | sort)
report "$out"

# A collector collects its whole directory. Reachability above catches a file
# nothing imports at all; it does not catch one that some other file imports by
# exact path while its own directory's `API.lean` leaves it out — which is how
# `Global/Block.lean` sat outside `Global/API.lean` with the build still green.
#
# "Its whole directory" is every sibling `.lean` file and every sub-directory,
# the latter reduced to its own collector where it has one. An omission that is
# meant says so on one line of the collector's docstring, so the exception lives
# beside the imports it is about rather than in a list here, which would go
# stale exactly the way the prose does. A marker that excuses nothing is
# reported too, so it cannot outlive its reason.
#
# Reads the same list file as the walk above, and for the same reason: a split
# argument list would hand it a partial tree.
out=$(awk -v LIST="$list" '
BEGIN {
  while ((getline f < LIST) > 0)
    if (f != "") { ARGV[ARGC++] = f; nfiles++; all[nfiles] = f; isFile[f] = 1 }
}
function moduleOf(path,   m) {
  m = path; sub(/^src\//, "", m); sub(/\.lean$/, "", m); gsub("/", ".", m)
  return m
}
function dirOf(path,   d) { d = path; sub(/\/[^\/]*$/, "", d); return d }
function baseOf(path,   b) { b = path; sub(/^.*\//, "", b); return b }

FNR == 1 { mod = moduleOf(FILENAME) }
/^(public[ \t]+)?(meta[ \t]+)?import[ \t]/ {
  dep = $0; sub(/^(public[ \t]+)?(meta[ \t]+)?import[ \t]+/, "", dep); sub(/[ \t]+$/, "", dep)
  imp[mod, dep] = 1
}
# The one form the marker takes, so that finding it needs no judgement.
/`[^`]+` is deliberately not collected here/ {
  match($0, /`[^`]+` is deliberately not collected here/)
  lbl = substr($0, RSTART + 1, RLENGTH - 1); sub(/`.*$/, "", lbl)
  if (!((mod, lbl) in excuse)) excuse[mod, lbl] = FNR
}

# What module stands for a directory: its `API.lean`, or the `<dir>.lean` beside
# it — `src/CORALean.lean` and `Examples/Demo.lean` are collectors of that shape.
function entryOf(d) {
  if ((d "/API.lean") in isFile) return moduleOf(d "/API.lean")
  if ((d ".lean") in isFile) return moduleOf(d ".lean")
  return ""
}
function addWant(m, lbl) {
  if (m == "" || m == curMod || (m in wantLbl)) return
  nwant++; wantMod[nwant] = m; wantLbl[m] = lbl
}
# Everything directory `d` holds, labelled by its path under the collector: a
# sibling file as itself, a sub-directory as its entry point, and a
# sub-directory with no entry point walked through to the files inside it.
function expand(d, prefix,   n, i, arr, e) {
  n = split(fileIn[d], arr, " ")
  for (i = 1; i <= n; i++)
    if (arr[i] != "") addWant(moduleOf(d "/" arr[i]), prefix arr[i])
  n = split(subIn[d], arr, " ")
  for (i = 1; i <= n; i++) {
    if (arr[i] == "") continue
    e = entryOf(d "/" arr[i])
    if (e != "") addWant(e, prefix arr[i] "/")
    else expand(d "/" arr[i], prefix arr[i] "/")
  }
}
# A marker naming a sub-directory excuses everything under it, so one line
# covers a `Float/` that holds twenty files.
function excused(m, lbl,   p) {
  if ((m, lbl) in excuse) { used[m, lbl] = 1; return 1 }
  p = lbl
  while (sub(/[^\/]*$/, "", p) && p != "") {
    if ((m, p) in excuse) { used[m, p] = 1; return 1 }
    sub(/\/$/, "", p)
  }
  return 0
}
END {
  # The tree, from the file list: what each directory holds directly, and which
  # directories sit under it.
  for (i = 1; i <= nfiles; i++) {
    d = dirOf(all[i])
    fileIn[d] = fileIn[d] " " baseOf(all[i])
    cur = d
    while (cur ~ /\//) {
      par = dirOf(cur); nm = baseOf(cur)
      if (!((par, nm) in kid)) { kid[par, nm] = 1; subIn[par] = subIn[par] " " nm }
      cur = par
    }
  }
  for (i = 1; i <= nfiles; i++) {
    c = all[i]
    if (c ~ /\/API\.lean$/) d = dirOf(c)
    else if (c == "src/CORALean.lean") d = "src/CORALean"
    else continue
    curMod = moduleOf(c)
    split("", wantMod); split("", wantLbl); nwant = 0
    expand(d, "")
    for (j = 1; j <= nwant; j++) {
      m = wantMod[j]
      if ((curMod, m) in imp || excused(curMod, wantLbl[m])) continue
      print c ":1: does not collect `" wantLbl[m] "` — import `" m "`, or say in the" \
            " module docstring that `" wantLbl[m] "` is deliberately not collected here"
    }
    for (k in excuse) {
      split(k, kp, SUBSEP)
      if (kp[1] == curMod && !((kp[1], kp[2]) in used))
        print c ":" excuse[k] ": `" kp[2] "` is marked deliberately not collected," \
              " but this directory holds no such thing"
    }
  }
}
' | sort)
report "$out"

fi

# The proof flag. A statement that wraps over several lines does not obviously
# end, so a declaration's `:= by` carries `-- --- PROOF ---` once its proof runs
# to five lines or more, or its signature does (from the `theorem`/`lemma` line to
# the `:= by` line, inclusive) — the point where the seam stops being visible at a
# glance. Required there and refused when both are shorter, so the flag always
# means the same thing; and only on the declaration's own `:= by`, never on a nested
# `have ... := by`, since a flag on every inner block marks nothing.
out=$(printf '%s\n' "$files" | xargs awk -v MIN=5 '
function isdecl(s) {
  return s ~ /^(@\[[^]]*\][ \t]*)?(private |protected |noncomputable |scoped )*(theorem|lemma)[ \t]/
}
function checkfile(   i, j, k, n, last, end, s, tagged) {
  split("", legit)
  i = 1
  while (i <= nf) {
    if (!isdecl(L[i])) { i++; continue }
    end = 0
    for (j = i; j <= nf && j - i < 30; j++) {
      if (j > i && L[j] ~ /^[^ \t]/) break   # a signature runs on indented: the next declaration or banner ends it
      s = L[j]; sub(/[ \t]+$/, "", s)
      if (s ~ / where$/) break        # proved by a structure instance: no `:= by` of its own
      if (s ~ /:= by$/ || s ~ /:= by -- --- PROOF ---$/) { end = j; break }
    }
    if (end == 0) { i++; continue }
    k = end + 1; last = end
    while (k <= nf && (L[k] ~ /^  / || L[k] ~ /^[ \t]*$/)) {
      if (L[k] !~ /^[ \t]*$/) last = k
      k++
    }
    n = last - end        # the proof, not the blank lines between it and what follows
    sig = end - i + 1     # the signature, `theorem` line to `:= by` line inclusive
    legit[end] = 1
    s = L[end]; sub(/[ \t]+$/, "", s)
    tagged = (s ~ /:= by -- --- PROOF ---$/)
    if ((n >= MIN || sig >= MIN) && !tagged)
      print fname ":" end ": a proof of " n " lines after a signature of " sig " lines needs" \
            " `-- --- PROOF ---` after its `:= by` — wrap the statement if the line has no room"
    if (n < MIN && sig < MIN && tagged)
      print fname ":" end ": the proof flag marks a proof of " n " lines after a signature of " sig \
            " lines — it is for " MIN " or more of either"
    i = k
  }
  for (i = 1; i <= nf; i++) {
    if (L[i] ~ /-- --- PROOF ---/ && !(i in legit))
      print fname ":" i ": the proof flag belongs on a declaration`s own `:= by`," \
            " not on a nested `have ... := by`"
    else if (L[i] ~ /:= by[ \t]*--/ && tolower(L[i]) ~ /proof/ && L[i] !~ /:= by -- --- PROOF ---$/)
      print fname ":" i ": the proof flag reads `-- --- PROOF ---`, exactly, after `:= by`"
  }
}
FNR == 1 { if (nf > 0) checkfile(); split("", L); nf = 0; fname = FILENAME }
{ L[++nf] = $0 }
END { if (nf > 0) checkfile() }
' | sort)
report "$out"

# Mathlib is imported in the file that uses it, never through a shared one: a
# shared file makes every importer rebuild when any import is added to it. So no
# file may be `Global/Mathlib.lean`, and none may hold nothing but `import
# Mathlib.*` lines (comments and blanks aside).
out=$(printf '%s\n' "$files" | awk '
$0 == "src/CORALean/Global/Mathlib.lean" {
  print $0 ": a shared Mathlib import file — import Mathlib modules in the file that uses them"
}' )
out="$out
$(awk '
FNR == 1 { if (n > 0 && other == 0) print prev ": holds only `import Mathlib.*` lines —" \
             " import Mathlib modules in the file that uses them"
           prev = FILENAME; n = 0; other = 0; inb = 0 }
{
  s = $0
  if (inb) { if (s ~ /-\//) { inb = 0; sub(/^.*-\//, "", s) } else next }
  while (s ~ /\/-/) {
    pre = s; sub(/\/-.*$/, "", pre); post = s; sub(/^.*\/-/, "", post)
    if (post ~ /-\//) { sub(/^.*-\//, "", post); s = pre post } else { s = pre; inb = 1 }
  }
  sub(/--.*$/, "", s)
  if (s ~ /^[ \t]*$/) next
  # `module` and the section a module opens are header, not content.
  if (s == "module" || s ~ /^@\[expose\] public section/) next
  if (s ~ /^(public[ \t]+)?(meta[ \t]+)?import[ \t]+Mathlib\./) n++; else other++
}
END { if (n > 0 && other == 0) print prev ": holds only `import Mathlib.*` lines —" \
        " import Mathlib modules in the file that uses them" }
' $files)"
report "$(printf '%s' "$out" | sed '/^$/d')"

if [ -z "$STAGED" ]; then

# The float layer names its types as the exact layer does, the layer being the
# namespace: `Float.Zonotope (Vec 𝕋 n)` beside `Real.Zonotope (Vec ℝ n)`, never a
# `GZonotope` with a `Zonotope 𝕋 n` abbreviation in front of it, nor a
# `StarSetFloat` beside `StarSet`. Four rules, from the declarations alone:
#   (1) no `structure`/`inductive`/`class`/`abbrev` named `G<Name>` where
#       `<Name>` is a type the Real layer declares (a `Real/` folder or a
#       `...Real` namespace);
#   (2) no top-level type `<Name>Float` where `<Name>` is a declared type — in
#       `CORALean`, `CORALean.Float` or `CORALean.Real` the namespace says the
#       layer — while one nested in another namespace is allowed, as
#       `LinearSys.AutoStateFloat`: a system namespace is not split by layer,
#       its plain name is the algorithm of the paper and `...Float` its sound
#       rounded-arithmetic implementation (`reach`, `reachFloat`);
#   (3) a representation `ContSet/<S>/` with both `Real/<S>.lean` and
#       `Float/<S>.lean` declares the same main type in both, the first type
#       after the MAIN TYPE banner;
#   (4) no `abbrev` under `Float/` that aliases a representation at `Vec`, a
#       right-hand side starting with the type (or a `G` of it) and holding `(Vec`.
out=$(awk -v LIST="$list" '
BEGIN {
  while ((getline f < LIST) > 0) if (f != "") ARGV[ARGC++] = f
  DECL = "^(@\\[[^]]*\\][ \t]*)?((private|protected|noncomputable|scoped|partial|unsafe)[ \t]+)*" \
         "(structure|inductive|class|abbrev)[ \t]+"
}
function lastOf(s,   b) { b = s; sub(/^.*\./, "", b); return b }
FNR == 1 {
  inb = 0; nst = 0; banner = 0
  fileReal = (FILENAME ~ /\/Real\//)
  if (match(FILENAME, /\/ContSet\/[^\/]+\/(Real|Float)\/[^\/]+\.lean$/)) {
    seg = substr(FILENAME, RSTART + 9, RLENGTH - 9)   # <S>/<Layer>/<file>.lean
    split(seg, sp, "/"); rep = sp[1]; layer = sp[2]; fb = sp[3]; sub(/\.lean$/, "", fb)
    isMain = (fb == rep)
  } else { isMain = 0 }
}
{
  s = $0
  if (inb) { if (s ~ /-\//) inb = 0; next }
  if (s ~ /^[ \t]*\/-/ && s !~ /-\//) { inb = 1; next }
  if (s ~ /MAIN TYPE/) banner = 1
  if (s ~ /^namespace[ \t]/) { st[++nst] = $2; next }
  if (s ~ /^section([ \t]|$)/) { st[++nst] = "§"; next }
  if (s ~ /^end([ \t]|$)/) { if (nst > 0) nst--; next }
  if (s !~ DECL) next
  sub(DECL, "", s); name = s; sub(/[ \t:({\[].*$/, "", name)
  if (name == "") next
  full = name
  for (i = nst; i >= 1; i--) if (st[i] != "§") full = st[i] "." full
  base = lastOf(name)
  real = fileReal || ("." full ".") ~ /\.Real\./
  nd++; dName[nd] = name; dFull[nd] = full; dBase[nd] = base; dLoc[nd] = FILENAME ":" FNR
  declared[base] = 1
  if (real) realType[base] = 1
  if (isMain && banner && !((FILENAME) in mainOf)) {
    mainOf[FILENAME] = base; mainLoc[FILENAME] = FNR; mainKey[rep, layer] = FILENAME
  }
  # (4) a `Float/` abbreviation of a representation at `Vec`
  if ($0 ~ /^abbrev/ && FILENAME ~ /\/Float\// && index($0, ":=") > 0) {
    rhs = substr($0, index($0, ":=") + 2); sub(/^[ \t]+/, "", rhs)
    head = rhs; sub(/[ \t(].*$/, "", head); head = lastOf(head)
    if (rhs ~ /\(Vec[ \t]/) { nab++; abHead[nab] = head; abLoc[nab] = FILENAME ":" FNR; abName[nab] = name }
  }
}
END {
  # the representations: the main types of `ContSet/<S>/Real/<S>.lean`
  for (k in mainKey) { split(k, kp, SUBSEP); if (kp[2] == "Real") repType[mainOf[mainKey[k]]] = 1 }
  for (i = 1; i <= nd; i++) {
    b = dBase[i]
    if (b ~ /^G[A-Z]/ && (substr(b, 2) in realType))
      print dLoc[i] ": `" dName[i] "` — the float layer names this type `" substr(b, 2) \
            "`, as the Real layer does (rule 1, no `G` prefix)"
    if (b ~ /.Float$/ && (substr(b, 1, length(b) - 5) in declared)) {
      ns = dFull[i]; if (!sub(/\.[^.]*$/, "", ns)) ns = ""
      if (ns != "" && ns != "CORALean" && ns != "CORALean.Float" && ns != "CORALean.Real") continue
      print dLoc[i] ": `" dName[i] "` — a float twin of `" substr(b, 1, length(b) - 5) \
            "` takes its name and the `Float` namespace at the top level, not a `Float` suffix (rule 2)"
    }
  }
  for (k in mainKey) {
    split(k, kp, SUBSEP)
    if (kp[2] != "Float" || !((kp[1], "Real") in mainKey)) continue
    ff = mainKey[k]; rf = mainKey[kp[1], "Real"]
    if (mainOf[ff] != mainOf[rf])
      print ff ":" mainLoc[ff] ": the main type is `" mainOf[ff] "` but " rf " declares `" \
            mainOf[rf] "` — the two layers of a representation share its name (rule 3)"
  }
  for (i = 1; i <= nab; i++) {
    h = abHead[i]
    if ((h in repType) || (h ~ /^G[A-Z]/ && (substr(h, 2) in repType)))
      print abLoc[i] ": `abbrev " abName[i] "` aliases `" h "` at `Vec` — write `" \
            (h ~ /^G[A-Z]/ ? substr(h, 2) : h) " (Vec 𝕋 n)` at the use instead (rule 4)"
  }
}
' | sort)
report "$out"

fi

# No file may import the same module twice: union merges of merge trains leave
# repeated `import` lines in the collector files.
out=$(awk '
FNR == 1 { delete seen }
/^(public[ \t]+)?(meta[ \t]+)?import[ \t]/ { if (seen[$NF]++) print FILENAME ": duplicate import " $NF }
' $files)
report "$out"

if [ -z "$STAGED" ]; then

# A CI script line that starts with `!` never fails the job: the runner's `set -e`
# ignores a negated command's status. The warning gate was such a line and let a
# warning through to main.
out=$(grep -nE '^[[:space:]]*-[[:space:]]+"?![[:space:]]' .gitlab-ci.yml |
  sed 's/^\([0-9]*\):.*/.gitlab-ci.yml:\1: a script line negated with `!` cannot fail the job — use `if …; then exit 1; fi`/')
report "$out"

fi

# A set family is written with its notation, never as the lambda it abbreviates:
# `(S := 𝒵[𝕋])`, not `(S := fun k => Zonotope (Vec 𝕋 k))` (CONTRIBUTING, "Notation").
# The long form is allowed in the notation definitions themselves and where the
# notation is out of reach because the file does not import the representation's
# `Instances.lean` (imports are not added for a notation); a file listed here
# says so by name, and the list only shrinks.
FAMILY_LONG_FORM_OK=${FAMILY_LONG_FORM_OK:-scripts/family-notation-exceptions.txt}
out=$(printf '%s\n' "$files" | xargs grep -nE \
  'fun [^=]+ => ((CORALean\.)?(Real|Float)\.)?(Zonotope|Interval|ZonoBundle|VPolytope|PolyZonotope|HPolytope|ConZonotope|ConPolyZono) \((Vec|Mat) |fun [a-z]+ => Set \(Vec (ℝ|Real) ' |
  grep -v 'notation "' |
  awk -F: -v LIST="$FAMILY_LONG_FORM_OK" '
    BEGIN { while ((getline f < LIST) > 0) if (f !~ /^#/ && f != "") { split(f, w, " "); ok[w[1]] = 1 } }
    !($1 in ok) { print $1 ":" $2 ": a set family written as a lambda — use its notation (`𝒵[𝕋]`, `ℐ`, `𝒮`, …)" }')
report "$out"

# A declaration of at most five code lines is a section of its directory's
# `Basic.lean` (CONTRIBUTING, "Small declarations"). Reading sections, their
# order and the import cycles that keep a file out takes a real parse, so this
# rule is the one written in Python; CI's conventions job installs python3 for
# `check-references.py` already.
#
# The helper exits 1 when it has findings, which are on its stdout and go through
# `report` like every other pass; that status is the only one tolerated. Anything
# else, or a status of 1 with nothing printed, is the helper itself failing (a
# crash, an interpreter that is not one), and a check that did not run must not
# read as a check that passed.
bundle_err=$(mktemp)
if [ -n "$STAGED" ]; then
  # Run at the repository, which has the directories the exclusions look at, on
  # the index versions already checked out here.
  out=$(cd "$repo" && $PYTHON scripts/check-basic-bundles.py --files "$list" --stage "$stage" \
    2> "$bundle_err") && bundle_rc=0 || bundle_rc=$?
else
  out=$($PYTHON scripts/check-basic-bundles.py 2> "$bundle_err") && bundle_rc=0 || bundle_rc=$?
fi
if [ "$bundle_rc" -gt 1 ] || { [ "$bundle_rc" -eq 1 ] && [ -z "$out" ]; }; then
  cat "$bundle_err" >&2
  rm -f "$bundle_err"
  echo "check-conventions.sh: scripts/check-basic-bundles.py failed (status $bundle_rc) —" \
    "the Basic.lean bundles were not checked" >&2
  exit 2
fi
rm -f "$bundle_err"
report "$out"

# More rules that read a definition's body, whole-tree only (their allowlists need every
# file): a float definition that is only the exact operation at `nominal` (#154), a definition
# citing a paper's algorithm without its `-- <n>.` step comments (CONTRIBUTING, "Algorithms
# read like the paper"), a long subterm spelled out three times in one declaration, and a
# discrete-time class whose fields differ from its continuous twin's without a reason in
# scripts/dt-twin-allowlist.txt (#172), and a public theorem that exactly one other file reads
# and nothing outward-facing names (#189). Same contract as the helper above: status 1 with
# findings on stdout is a finding, anything else is the helper failing.
if [ -z "$STAGED" ]; then
  for helper in check-float-wrappers.py check-algorithm-steps.py check-repeated-subterms.py \
    check-dt-twins.py check-single-use.py; do
    helper_err=$(mktemp)
    out=$($PYTHON "scripts/$helper" 2> "$helper_err") && helper_rc=0 || helper_rc=$?
    if [ "$helper_rc" -gt 1 ] || { [ "$helper_rc" -eq 1 ] && [ -z "$out" ]; }; then
      cat "$helper_err" >&2
      rm -f "$helper_err"
      echo "check-conventions.sh: scripts/$helper failed (status $helper_rc) —" \
        "it was not checked" >&2
      exit 2
    fi
    rm -f "$helper_err"
    report "$out"
  done
fi

# Every declaration in a section under a `MAIN THEOREM`, `MAIN DEFINITION`, `MAIN TYPE` or
# `MAIN INSTANCE` banner carries a `/--` docstring, which is what a reader meets first: a
# main declaration without one makes the reader work out what it states or computes from the
# signature. Attributes (`@[simp]`) between the docstring and the declaration are fine.
# Files not yet brought up to this are listed in `scripts/main-docstring-allowlist.txt`, one
# path per line; the list only shrinks, and an entry whose file has no such declaration left
# is reported as stale.
out=$(awk -v LIST=scripts/main-docstring-allowlist.txt -v STALE="${STAGED:-}" '
BEGIN {
  while ((getline l < LIST) > 0) { if (l ~ /^#/ || l == "") continue; allow[l] = 1; aln[l] = ++n }
  close(LIST)
}
FNR == 1 { inb = 0; sect = 0; doc = 0; isdoc = 0; seen[FILENAME] = 1 }
{
  s = $0
  if (inb) { if (s ~ /-\//) { inb = 0; if (isdoc) doc = 1 }; next }
  if (s ~ /^[ \t]*\/-/) {
    isdoc = (s ~ /^[ \t]*\/--/)
    if (s !~ /-\//) inb = 1; else if (isdoc) doc = 1
    next
  }
  if (s ~ /^-- [-=]+  .*  [-=]+ --$/) { sect = (s ~ /MAIN (THEOREM|DEFINITION|TYPE|INSTANCE)/); doc = 0; next }
  if (s ~ /^[ \t]*--/ || s ~ /^[ \t]*$/) next
  if (s ~ /^@\[[^]]*\][ \t]*$/) next
  if (sect && s ~ /^(@\[[^]]*\][ \t]*)?((private|protected|noncomputable|nonrec|partial|scoped)[ \t]+)*(theorem|lemma|def|abbrev|structure|inductive|instance)[ \t]/ && !doc) {
    if (FILENAME in allow) hit[FILENAME] = 1
    else
      print FILENAME ":" FNR ": a main declaration without a `/--` docstring — say in words what it" \
            " states or computes"
  }
  doc = 0
}
END {
  if (STALE != "") exit
  for (f in allow)
    if (!(f in seen)) print LIST ":" aln[f] ": stale entry `" f "` — no such file"
    else if (!(f in hit)) print LIST ":" aln[f] ": stale entry `" f "` — no undocumented main declaration; the list only shrinks"
}' $files | sort)
report "$out"

# A main-type file holds the type and what it denotes, not what is said or done about
# it (CONTRIBUTING, "Main-type files"): the file with the `MAIN TYPE` banner at
# `<Dir>/<Dir>.lean` or `<Dir>/<Layer>/<Dir>.lean` has no `theorem`/`lemma`, and no
# `def`/`abbrev` named `materialise…`, the storage helper of the float sets, and no validity
# predicate (a declaration named `…Valid…`, `…WellFormed…`, `…Wf…`). Those go to
# `Theorems/`, `Operations/` and `Definitions/`, where the small ones share a `Basic.lean`.
out=$(awk '
function flush(   i) {
  if (banner && isMain)
    for (i = 1; i <= nh; i++)
      print file ":" hl[i] ": " hw[i] " in a main-type file — move it to `Theorems/`, `Operations/` or" \
            " `Definitions/` (a `Basic.lean` section when it is small)"
  nh = 0
}
FNR == 1 {
  flush()
  inb = 0; banner = 0; file = FILENAME
  n = split(FILENAME, pp, "/"); stem = pp[n]; sub(/\.lean$/, "", stem)
  isMain = (stem == pp[n-1] || stem == pp[n-2])
}
{
  s = $0
  if (inb) { if (s ~ /-\//) inb = 0; next }
  if (s ~ /^[ \t]*\/-/) { if (s !~ /-\//) inb = 1; next }
  if (s ~ /^-- =.*MAIN TYPE/) banner = 1
  if (s ~ /^[ \t]*--/ || !isMain) next
  if (s ~ /^(@\[[^]]*\][ \t]*)?((private|protected|nonrec)[ \t]+)*(theorem|lemma)[ \t]/) {
    nh++; hl[nh] = FNR; hw[nh] = "a theorem"
  } else if (s ~ /^(@\[[^]]*\][ \t]*)?((private|protected|noncomputable|nonrec)[ \t]+)*(def|abbrev)[ \t]+([A-Za-z0-9_.]*[.])?materialise/) {
    nh++; hl[nh] = FNR; hw[nh] = "storage (`materialise`)"
  } else if (s ~ /^(@\[[^]]*\][ \t]*)?((private|protected|noncomputable|nonrec)[ \t]+)*(def|abbrev|structure|inductive|class)[ \t]+([A-Za-z0-9_.]*[.])?[A-Za-z0-9_]*(Valid|WellFormed|Wf)[A-Za-z0-9_]*([ \t:({\[]|$)/) {
    nh++; hl[nh] = FNR; hw[nh] = "a validity predicate (`IsValid`, `WellFormed`, ...)"
  }
}
END { flush() }
' $files)
report "$out"
if [ -z "$STAGED" ]; then

# Layering: no file imports a directory the table forbids it, except the listed
# exceptions, and no exception outlives its import.
out=$(awk -v LAYERS="$LAYERS" -v EXC="$LAYER_EXCEPTIONS" '
BEGIN {
  n = split(LAYERS, ls, "\n")
  for (i = 1; i <= n; i++) {
    if (ls[i] !~ /:/) continue
    split(ls[i], kv, ":"); m = split(kv[2], ds, " ")
    for (j = 1; j <= m; j++) forbid[kv[1] "/" ds[j]] = 1
  }
  n = split(EXC, es, "\n")
  for (i = 1; i <= n; i++) {
    if (es[i] !~ /\|/) continue
    split(es[i], kv, " [|] ")
    # the directory column is a top-level directory, or a path prefix below one
    # (`ContSet/Interval`), which then admits only the imports under that prefix
    split(kv[2], dp, "/"); excline[kv[1] "/" kv[2]] = 1
    excpre[kv[1] "/" dp[1]] = excpre[kv[1] "/" dp[1]] " " kv[2]
    if (kv[3] == "") print "layering: exception for " kv[1] " has no reason"
  }
}
/^(public[ \t]+)?(meta[ \t]+)?import[ \t]+CORALean\./ {
  split(FILENAME, pp, "/"); from = pp[3]
  full = $NF; sub(/^CORALean\./, "", full); gsub(/\./, "/", full)
  to = full; sub(/\/.*/, "", to)
  if (to == from || !((from "/" to) in forbid)) next
  key = FILENAME "/" to
  m = split(excpre[key], pres, " "); ok = 0
  for (j = 1; j <= m; j++) {
    p = pres[j]
    if (p == to || index(full "/", p "/") == 1) { used[FILENAME "/" p] = 1; ok = 1 }
  }
  if (ok) next
  print FILENAME ": imports CORALean." to ", which " from "/ may not import (LAYERS in check-conventions.sh)"
}
END { for (k in excline) if (!(k in used)) print "layering: stale exception " k }
' $files)
report "$out"

# Import guards: the base files keep every guard, each with its comment, and
# `assert_not_imported` names a module that exists (a typo there guards nothing).
out=$(printf '%s\n' "$GUARDED_FILES" | while IFS='|' read -r gf gn; do
  gf=$(printf '%s' "$gf" | tr -d ' '); gn=$(printf '%s' "$gn" | tr -d ' ')
  [ -n "$gf" ] || continue
  awk -v WANT="$gn" '
  { prev = cur; cur = $0 }
  /^-- Import guards/ { marker = 1 }
  /^assert_not_(exists|imported)[ \t]/ {
    n++
    if (prev !~ /^-- /) print FILENAME ":" FNR ": guard without a comment line above it saying why"
    if ($1 == "assert_not_imported") {
      mp = "src/" $2; gsub(/\./, "/", mp); mp = mp ".lean"
      if (system("test -f " mp) != 0) print FILENAME ":" FNR ": " $2 " is not a module of this repository"
    }
  }
  END {
    if (!marker) print FILENAME ": missing the `-- Import guards` comment"
    if (n != WANT) print FILENAME ": has " n " import guards, GUARDED_FILES says " WANT " (change both on purpose)"
  }' "$gf"
done)
report "$out"

fi


# Interfaces (#177): a `class` declaration — `class`, `class inductive`, `class abbrev`, with any
# attributes and modifiers — only in an `Interfaces.lean`, or in a file `CLASS_LIST` names with a
# reason. Comments are stripped as in the per-file pass, so a docstring line starting with the
# word is not a declaration.
out=$(awk -v LIST="$list" -v CLASSLIST="$CLASS_LIST" \
  -v STALE="$([ -z "$STAGED" ] && echo 1 || echo 0)" '
function strip(line,   out, i, c, n) {
  out = ""; i = 1; n = length(line)
  while (i <= n) {
    c = substr(line, i, 2)
    if (depth == 0 && c == "--") break
    if (c == "/-") { depth++; i += 2; continue }
    if (c == "-/") { if (depth > 0) depth--; i += 2; continue }
    if (depth == 0) out = out substr(line, i, 1)
    i++
  }
  return out
}
BEGIN {
  while ((getline cl < CLASSLIST) > 0) {
    clFNR++
    line = cl
    sub(/^[ \t]+/, "", line)
    if (line == "" || line ~ /^#/) continue
    p = line; sub(/[ \t].*$/, "", p)
    r = line; sub(/^[^ \t]+[ \t]*/, "", r)
    if (p in classOK)
      print CLASSLIST ":" clFNR ": duplicate entry `" p "` (first at line " classLine[p] ")"
    if (r == "")
      print CLASSLIST ":" clFNR ": `" p "` carries no reason — say why its class is not in an" \
            " `Interfaces.lean`"
    if (p ~ /\/Interfaces\.lean$/)
      print CLASSLIST ":" clFNR ": `" p "` is an `Interfaces.lean`, which needs no entry"
    classOK[p] = 1; classLine[p] = clFNR
  }
  close(CLASSLIST)
  while ((getline f < LIST) > 0) {
    if (f == "") continue
    seen[f] = 1; depth = 0; ln = 0
    while ((getline raw < f) > 0) {
      ln++
      code = strip(raw)
      if (code !~ /^(@\[[^]]*\][ \t]*)*((private|protected|noncomputable|scoped)[ \t]+)*class[ \t]/)
        continue
      hasClass[f] = 1
      if (f ~ /\/Interfaces\.lean$/ || (f in classOK)) continue
      name = code; sub(/^.*class[ \t]+((inductive|abbrev)[ \t]+)?/, "", name); sub(/[ \t(:{\[].*$/, "", name)
      print f ":" ln ": class `" name "` declared outside an `Interfaces.lean` — move it to the" \
            " directory'"'"'s `Interfaces.lean`, or list the file in " CLASSLIST " with the reason"
    }
    close(f)
  }
  if (!STALE) exit
  for (p in classOK)
    if (!(p in seen))
      print CLASSLIST ":" classLine[p] ": stale entry `" p "` — no such file"
    else if (!(p in hasClass))
      print CLASSLIST ":" classLine[p] ": stale entry `" p "` — the file declares no class now;" \
            " the list only shrinks"
}' | sort)
report "$out"

# A float negation is written `-A` or `-b`, never as the lambda it abbreviates,
# `fun i j => neg (A i j)` / `fun i => neg (b i)` (#197): negation is exact, so the `Neg` on a
# float matrix or vector is the entrywise `neg`.
out=$(awk -v LIST="$list" '
function strip(line,   out, i, c, n) {
  out = ""; i = 1; n = length(line)
  while (i <= n) {
    c = substr(line, i, 2)
    if (depth == 0 && c == "--") break
    if (c == "/-") { depth++; i += 2; continue }
    if (c == "-/") { if (depth > 0) depth--; i += 2; continue }
    if (depth == 0) out = out substr(line, i, 1)
    i++
  }
  return out
}
BEGIN {
  while ((getline f < LIST) > 0) {
    if (f == "") continue
    depth = 0; ln = 0
    while ((getline raw < f) > 0) {
      ln++
      rest = strip(raw)
      while (match(rest, /fun [a-z][a-z'"'"']*( [a-z][a-z'"'"']*)? => (Float[.])?(FloatOps[.])?neg \(/)) {
        head = substr(rest, RSTART, RLENGTH); rest = substr(rest, RSTART + RLENGTH)
        sub(/^fun /, "", head); sub(/ =>.*$/, "", head); nb = split(head, bs, " ")
        if (!match(rest, /^[^()]*\)/)) continue
        body = substr(rest, 1, RLENGTH - 1); after = substr(rest, RLENGTH + 1, 1)
        n = split(body, ts, " "); ok = (n >= nb + 1 && after !~ /[.[]/)
        for (k = 1; ok && k <= nb; k++) if (ts[n - nb + k] != bs[k]) ok = 0
        if (ok)
          print f ":" ln ": a float negation written as a lambda — write `-A` / `-b` (`Neg` on a" \
                " float matrix or vector is the entrywise `neg`)"
      }
    }
    close(f)
  }
}' | sort)
report "$out"

# No `theorem` or `lemma` in an `Operations/` file but those `OPS_THEOREM_LIST` names (#198).
# Comments are stripped as in the class rule above.
out=$(awk -v LIST="$list" -v OPSLIST="$OPS_THEOREM_LIST" \
  -v STALE="$([ -z "$STAGED" ] && echo 1 || echo 0)" '
function strip(line,   out, i, c, n) {
  out = ""; i = 1; n = length(line)
  while (i <= n) {
    c = substr(line, i, 2)
    if (depth == 0 && c == "--") break
    if (c == "/-") { depth++; i += 2; continue }
    if (c == "-/") { if (depth > 0) depth--; i += 2; continue }
    if (depth == 0) out = out substr(line, i, 1)
    i++
  }
  return out
}
BEGIN {
  while ((getline ol < OPSLIST) > 0) {
    opsFNR++
    line = ol
    sub(/^[ \t]+/, "", line)
    if (line == "" || line ~ /^#/) continue
    p = line; sub(/[ \t].*$/, "", p)
    if (p in opsOK)
      print OPSLIST ":" opsFNR ": duplicate entry `" p "` (first at line " opsLine[p] ")"
    opsOK[p] = 1; opsLine[p] = opsFNR
  }
  close(OPSLIST)
  while ((getline f < LIST) > 0) {
    if (f == "") continue
    seen[f] = 1; depth = 0; ln = 0
    inOps = (f ~ /\/Operations\//)
    while ((getline raw < f) > 0) {
      ln++
      code = strip(raw)
      if (!inOps ||
          code !~ /^(@\[[^]]*\][ \t]*)*((private|protected|nonrec|local)[ \t]+)*(theorem|lemma)[ \t]/)
        continue
      hasThm[f] = 1
      if (!(f in opsOK) && !(f in reported)) {
        reported[f] = 1
        print f ":" ln ": a theorem in an `Operations/` file — state it in a `Theorems/` file, or" \
              " in the global lemmas if it is a general fact (or list the file in " OPSLIST \
              " until it is moved)"
      }
    }
    close(f)
  }
  if (!STALE) exit
  for (p in opsOK)
    if (!(p in seen))
      print OPSLIST ":" opsLine[p] ": stale entry `" p "` — no such file"
    else if (!(p in hasThm))
      print OPSLIST ":" opsLine[p] ": stale entry `" p "` — the file declares no theorem now;" \
            " the list only shrinks"
}' | sort)
report "$out"

# CORA spells it `center` (`centerMat`, `recenter`, `IsCenter`, …), so no `centre` in a source
# file, whether in an identifier, a docstring, a comment or the file's name (#199).
out=$(awk -v LIST="$list" '
BEGIN {
  while ((getline f < LIST) > 0) {
    if (f == "") continue
    if (f ~ /[Cc]entre/)
      print f ": `centre` in a file name — CORA spells it `center`"
    ln = 0
    while ((getline raw < f) > 0) {
      ln++
      if (raw ~ /[Cc]entre/)
        print f ":" ln ": `centre` — CORA spells it `center` (`centerMat`, `recenter`, …)"
    }
    close(f)
  }
}' | sort)
report "$out"

if [ "$status" -eq 0 ]; then
  if [ -n "$STAGED" ]; then
    printf 'conventions: %s staged files, per-file rules passed\n' "$(printf '%s\n' "$files" | wc -l | tr -d ' ')"
  else
    printf 'conventions: %s files, all checks passed\n' "$(printf '%s\n' "$files" | wc -l | tr -d ' ')"
  fi
fi

exit "$status"

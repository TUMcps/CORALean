#!/bin/sh
# Checks the conventions CONTRIBUTING.md states, none of which the compiler can
# check: a green build says nothing about whether `aux_` stayed in its file or
# whether an `API.lean` slipped a declaration in.
#
# Text only — no Lean, no build, no network — so it runs in a second, on a
# pre-commit hook as well as in CI. That is why the parsing is deliberately
# shallow: comments are stripped by a two-character scanner and declarations are
# matched at the start of a line. It reports what is wrong, never rewrites.
#
# POSIX sh and awk, so it runs in CI and in Git Bash on Windows alike.

set -eu

# Byte semantics everywhere, so the checks read the same under gawk and mawk;
# `charlen` is what turns bytes back into characters where that is what is
# meant. Without this a line of ℝ and ⊆ counts as over-long in CI and not here.
LC_ALL=C
export LC_ALL

cd "$(dirname "$0")/.."

status=0

report() {
  if [ -n "$1" ]; then
    printf '%s\n' "$1"
    status=1
  fi
}

files=$(find src -name '*.lean' | sed 's#\\#/#g' | sort)

# Per-file conventions, one pass. `depth` tracks nesting of `/- -/` across
# lines, so a docstring mentioning `aux_` or `sorry` is not mistaken for code.
out=$(printf '%s\n' "$files" | xargs awk '
BEGIN { CONT = "[\200-\277]" }

# Characters, not bytes: every byte of a UTF-8 sequence but the first is a
# continuation byte, so dropping those counts the characters.
function charlen(s,   t) { t = s; gsub(CONT, "", t); return length(t) }

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

function base(name,   k) {
  k = split(name, parts, "\\.")
  return parts[k]
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

function check(f,   i, n, collector, want, dir) {
  collector = (f ~ /\/API\.lean$/) || (f == "src/CORALean.lean") ||
              (f == "src/CORALean/Global/Mathlib.lean")

  for (a in useAux)
    if (!(a in declAux))
      say(f ":" useAux[a] ": `aux_` name `" a "` is not declared in this file")

  if (docLine == 0)
    say(f ":1: no module docstring — every file opens with `/-! ... -/`")

  if (collector) {
    if (authorLine > 0)
      say(f ":" authorLine ": a collector carries no author block")
    if (f ~ /\/API\.lean$/ && codeLine > 0)
      say(f ":" codeLine ": `API.lean` holds nothing but imports")
  } else if (authorLine == 0) {
    say(f ":1: no author block — content files carry one")
  }

  dir = dirOf(f)
  want = moduleOf(dir "/API.lean")
  for (i = 1; i <= nimp; i++) {
    if (imp[i] == want)
      say(f ":" impLine[i] ": imports the `API.lean` of its own directory, which is a cycle")
    if (f ~ /\/Real\// && f !~ /\/Float\// && imp[i] ~ /\.Float\./)
      say(f ":" impLine[i] ": a `Real` file must not import `Float`")
  }

  if (f ~ /\/Conversion\// && !(f ~ /\/API\.lean$/) &&
      !(f ~ /\/[A-Za-z]+_to_[A-Za-z]+\.lean$/))
    say(f ":1: a file in `Conversion/` is named `<Source>_to_<Target>.lean`")
}

function say(msg) { print msg }

FNR == 1 {
  if (prev != "") check(prev)
  prev = FILENAME
  depth = 0; nimp = 0; docLine = 0; authorLine = 0; codeLine = 0
  # `split("", a)` rather than `delete a`, which older mawk does not have
  split("", declAux); split("", useAux); split("", imp); split("", impLine)
}

{
  raw = $0
  if (charlen(raw) > 100)
    say(FILENAME ":" FNR ": line is " charlen(raw) " characters, over the limit of 100")
  if (raw ~ /[ \t]$/)
    say(FILENAME ":" FNR ": trailing whitespace")
  if (raw ~ /\t/)
    say(FILENAME ":" FNR ": tab character")
  if (docLine == 0 && raw ~ /^\/-!/) docLine = FNR
  if (authorLine == 0 && raw ~ /^-- Authors:/) authorLine = FNR

  code = strip(raw)

  if (code ~ /^import /) {
    nimp++
    imp[nimp] = code
    sub(/^import[ \t]+/, "", imp[nimp])
    sub(/[ \t]+$/, "", imp[nimp])
    impLine[nimp] = FNR
  } else if (code ~ /[^ \t]/) {
    if (codeLine == 0) codeLine = FNR
  }

  if (code ~ /(^|[^A-Za-z0-9_'"'"'.])sorry([^A-Za-z0-9_'"'"']|$)/)
    say(FILENAME ":" FNR ": `sorry`")
  if (code ~ /^axiom[ \t]/)
    say(FILENAME ":" FNR ": `axiom` — nothing here is axiomatised")

  if (code ~ /^(private |protected |noncomputable |partial |scoped )*(def|theorem|lemma|abbrev|instance|structure|inductive|class) /) {
    decl = code
    sub(/^(private |protected |noncomputable |partial |scoped )*(def|theorem|lemma|abbrev|instance|structure|inductive|class)[ \t]+/, "", decl)
    sub(/[^A-Za-z0-9_'"'"'.].*$/, "", decl)
    if (base(decl) ~ /^aux_/) declAux[base(decl)] = FNR
  }

  rest = code
  while (match(rest, /aux_[A-Za-z0-9_'"'"']*/)) {
    tok = substr(rest, RSTART, RLENGTH)
    if (!(tok in useAux)) useAux[tok] = FNR
    rest = substr(rest, RSTART + RLENGTH)
  }
}

END { if (prev != "") check(prev) }
')
report "$out"

# Every module reachable from a root, so a file that was written but never
# collected is caught rather than silently left out of the build. The roots are
# the roots of the targets `lakefile.toml` names, and a new target belongs in
# both places.
#
# The file list reaches awk through a list file rather than the command line.
# `xargs` splits an argument list that does not fit — on Windows the limit is
# 32 KB, and the environment a git hook adds is enough to cross it at this
# repository size — and each batch would then walk a partial import graph and
# report every module it happened not to see an importer for. The per-file pass
# above tolerates a split; this one cannot, since it is global by nature.
list=$(mktemp)
trap 'rm -f "$list"' EXIT INT TERM
printf '%s\n' "$files" > "$list"

out=$(awk -v LIST="$list" -v ROOTS="CORALean CORALean.Examples.API Demo" '
BEGIN { while ((getline f < LIST) > 0) if (f != "") ARGV[ARGC++] = f }
function moduleOf(path,   m) {
  m = path; sub(/^src\//, "", m); sub(/\.lean$/, "", m); gsub("/", ".", m)
  return m
}
FNR == 1 { mod = moduleOf(FILENAME); known[mod] = 1; depth = 0 }
/^import / {
  dep = $0; sub(/^import[ \t]+/, "", dep); sub(/[ \t]+$/, "", dep)
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

if [ "$status" -eq 0 ]; then
  printf 'conventions: %s files, all checks passed\n' "$(printf '%s\n' "$files" | wc -l | tr -d ' ')"
fi

exit "$status"

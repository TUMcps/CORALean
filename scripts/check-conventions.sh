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

# The numeric limits, gathered here because every one of them is a judgement
# call and the tree is the evidence for it. Each is at or just above the trimmed
# tree's worst case, so raising one is a decision rather than a drift.
MAX_LINE=100          # characters, not bytes
MAX_MODULE_DOC=20     # module docstring, content file
MAX_COLLECTOR_DOC=25  # module docstring, collector: it is the directory entry point
MAX_DECL_DOC=3        # docstring ahead of a declaration
MAX_LINES_WO_COMMENT=20  # a minimum density, not a maximum: proofs need signposts
MAX_PUBLIC_DECL=1     # public declarations per `Operations/`/`Theorems/` file (#62)

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
out=$(printf '%s\n' "$files" | xargs awk \
  -v MAX_LINE="$MAX_LINE" \
  -v MAX_MODULE_DOC="$MAX_MODULE_DOC" \
  -v MAX_COLLECTOR_DOC="$MAX_COLLECTOR_DOC" \
  -v MAX_DECL_DOC="$MAX_DECL_DOC" \
  -v MAX_LINES_WO_COMMENT="$MAX_LINES_WO_COMMENT" \
  -v MAX_PUBLIC_DECL="$MAX_PUBLIC_DECL" '
BEGIN {
  CONT = "[\200-\277]"
  MONTH = "(January|February|March|April|May|June|July|August|September|October|November|December)"
  DATE = "^(0[1-9]|[12][0-9]|3[01])-" MONTH "-[0-9][0-9][0-9][0-9]$"

  # A declaration, optionally carrying one attribute — `@[simp] theorem …` is as
  # much a declaration as `theorem …`, and every rule that scans for one needs to
  # see both alike. Built from octal escapes, not `\\[` `\\]` literals: this
  # awk drops a backslash ahead of a bracket in a string constant instead of
  # keeping it escaped, silently turning the pattern into a character class.
  BSLASH = "\134"; LBRACK = "\133"; RBRACK = "\135"
  ATTR = "(@" BSLASH LBRACK "[^" RBRACK "]*" BSLASH RBRACK "[ \t]*)?"
  MODS = "(private |protected |noncomputable |partial |scoped )*"
  KIND = "(def|theorem|lemma|abbrev|instance|structure|inductive|class)"
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

function check(f,   i, n, collector, want, dir, cap) {
  endRun(f)
  collector = (f ~ /\/API\.lean$/) || (f == "src/CORALean.lean") ||
              (f == "src/CORALean/Global/Mathlib.lean")

  for (a in useAux)
    if (!(a in declAux))
      say(f ":" useAux[a] ": `aux_` name `" a "` is not declared in this file")

  if (docLine == 0) {
    say(f ":1: no module docstring — every file opens with `/-! ... -/`")
  } else {
    cap = collector ? MAX_COLLECTOR_DOC : MAX_MODULE_DOC
    if (docLen > cap)
      say(f ":" docLine ": module docstring is " docLen " lines, over " cap \
          " — keep what is non-obvious about this file and drop the rest")
  }

  if (collector) {
    if (authorLine > 0)
      say(f ":" authorLine ": a collector carries no author block")
    if (f ~ /\/API\.lean$/ && codeLine > 0)
      say(f ":" codeLine ": `API.lean` holds nothing but imports")
  } else if (authorLine == 0) {
    say(f ":1: no author block — content files carry one, after the module docstring")
  } else if (docLine > 0 && authorLine != docEnd + 2) {
    say(f ":" authorLine ": the author block goes one blank line under the module" \
        " docstring, which ends at line " docEnd)
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
  # a name promoted for reuse without earning its own file (issue #62).
  if (f ~ /\/(Operations|Theorems)\// && !(f ~ /\/API\.lean$/) && npub > MAX_PUBLIC_DECL) {
    decls = pubList[1]
    for (i = 2; i <= npub; i++) decls = decls ", " pubList[i]
    say(f ":1: " npub " public declarations, over " MAX_PUBLIC_DECL \
        " — rename file-local ones `aux_...`, or split into one file each: " decls)
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

  # A layer directory and the namespace it declares must agree, since the path
  # is what a reader navigates by and the namespace is what Lean resolves by.
  if (!collector && nsLine > 0) {
    if (f ~ /\/Float\// && ns !~ /(^|\.)Float(\.|$)/)
      say(f ":" nsLine ": a file under `Float/` declares `namespace ...Float`, not `" ns "`")
    if (f ~ /\/Real\// && f !~ /\/Float\// && ns !~ /(^|\.)Real(\.|$)/)
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
    if (mainishCount == 0)
      say(f ":1: missing the `MAIN ...` marker before the main declaration of the file")
    else if (mainishCount > 1)
      say(f ":" pendingMainFNR ": more than one `MAIN ...`/`INSTANCES` marker")

    if (beginFNR > 0 && nsLine > 0 && beginFNR > nsLine)
      say(f ":" beginFNR ": `BEGIN CODE` must come before `namespace`")
    if (beginFNR > 0 && authorLine > 0 && beginFNR < authorLine)
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
  authorLine = 0; codeLine = 0; nsLine = 0; ns = ""
  blockKind = ""; blockStart = 0; declDocEnd = 0
  prevPureComment = 0; prevLineComment = 0; run = 0; blanks = 0; inRefs = 0; refsLine = 0
  firstDeclSeen = 0; firstBodyFound = 0; firstBodyLine = 0
  npub = 0; nDeclTotal = 0; lastFNR = 0
  beginCount = 0; endCount = 0; auxCount = 0; mainishCount = 0
  beginFNR = 0; endFNR = 0
  afterPending = 0; afterLabel = ""; afterMarkerFNR = 0; afterBlanks = 0
  pendingMain = 0; pendingMainLabel = ""; pendingMainFNR = 0; pendingMainIsInstances = 0
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
  } else if (raw ~ /^-- [-=]/) {
    say(FILENAME ":" FNR ": looks like a section marker but does not match the" \
        " canonical form — check the width and the fill either side of the label")
  }

  if (charlen(raw) > MAX_LINE)
    say(FILENAME ":" FNR ": line is " charlen(raw) " characters, over the limit of " \
        MAX_LINE " — wrap it")
  if (raw ~ /[ \t]$/)
    say(FILENAME ":" FNR ": trailing whitespace — strip it")
  if (raw ~ /\t/)
    say(FILENAME ":" FNR ": tab character — indent with spaces")
  if (raw !~ /[^ \t]/) { blanks++; if (blanks == 3) say(FILENAME ":" FNR \
      ": third blank line in a row — one blank line separates, two at most") }
  else blanks = 0
  if (authorLine == 0 && raw ~ /^-- Authors:/) authorLine = FNR

  # The author block, field by field, so that a block that is present but
  # malformed is caught rather than counted as present.
  if (authorLine > 0 && FNR >= authorLine && FNR <= authorLine + 3) {
    field = ""
    if (FNR == authorLine) field = "Authors:      "
    else if (FNR == authorLine + 1) field = "Written:      "
    else if (FNR == authorLine + 2) field = "Last update:  "
    else field = "Last revision:"
    lbl = field; sub(/[ \t]*$/, "", lbl)
    if (index(raw, "-- " field " ") != 1) {
      say(FILENAME ":" FNR ": the author block reads `-- " lbl \
          "` here, aligned to one column")
    } else {
      val = substr(raw, length("-- " field " ") + 1)
      sub(/[ \t]+$/, "", val)
      if (FNR == authorLine) {
        if (val !~ /^[A-Z]/)
          say(FILENAME ":" FNR ": `Authors:` names a person")
      } else if (FNR == authorLine + 1) {
        if (val !~ DATE)
          say(FILENAME ":" FNR ": `Written:` is a DD-Month-YYYY date, not `" val "`")
      } else if (val != "---" && val !~ DATE) {
        say(FILENAME ":" FNR ": `" lbl "` is a DD-Month-YYYY date or `---`, not `" val "`")
      }
    }
  }
  isAuthorBlock = (authorLine > 0 && FNR >= authorLine && FNR <= authorLine + 3)

  depthBefore = depth
  code = strip(raw)

  if (depthBefore == 0 && opened != "") { blockKind = opened; blockStart = FNR }
  lineKind = blockKind
  if (depth == 0 && blockKind != "") closeBlock(FNR)

  # References live in the module docstring; everything else that names a
  # number in brackets is citing one.
  if (lineKind == "mod") {
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
  if (authorLine > 0 && FNR > authorLine + 3 && firstBodyFound && FNR > firstBodyLine) {
    if (sawComment || lineKind != "") {
      endRun(FILENAME)
    } else if (code ~ /[^ \t]/) {
      if (run == 0) runStart = FNR
      run++
    }
  }

  if (code ~ /^import /) {
    nimp++
    imp[nimp] = code
    sub(/^import[ \t]+/, "", imp[nimp])
    sub(/[ \t]+$/, "", imp[nimp])
    impLine[nimp] = FNR
  } else if (code ~ /[^ \t]/) {
    if (codeLine == 0) codeLine = FNR
  }

  if (nsLine == 0 && code ~ /^namespace /) {
    ns = code; sub(/^namespace[ \t]+/, "", ns); sub(/[ \t].*$/, "", ns)
    nsLine = FNR
  }

  if (code ~ /(^|[^A-Za-z0-9_'"'"'.])sorry([^A-Za-z0-9_'"'"']|$)/)
    say(FILENAME ":" FNR ": `sorry` — finish the proof or drop the declaration")
  if (code ~ /^axiom[ \t]/)
    say(FILENAME ":" FNR ": `axiom` — nothing here is axiomatised")

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
    nDeclTotal++

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

    # A `Cost/` directory holds asserted running costs and nothing derived from
    # a definition; the `...Cost` name is one of the three things that says so,
    # the directory and the `Cost`-valued `def` being the other two.
    if (FILENAME ~ /\/Cost\// && kind == "def" && b !~ /^aux_/ && b !~ /(Cost|Bound)$/)
      say(FILENAME ":" FNR ": a `def` under `Cost/` is an asserted cost, named" \
          " `...Cost` or `...Bound`, not `" b "`")

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

out=$(awk -v LIST="$list" -v ROOTS="CORALean CORALean.Examples.API CORALean.Examples.Demo" '
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

# The proof flag. A statement that wraps over several lines does not obviously
# end, so a declaration's `:= by` carries `-- --- PROOF ---` once its proof runs
# to five lines or more — the point where the seam stops being visible at a
# glance. Required there and refused below it, so the flag always means the same
# thing; and only on the declaration's own `:= by`, never on a nested
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
    legit[end] = 1
    s = L[end]; sub(/[ \t]+$/, "", s)
    tagged = (s ~ /:= by -- --- PROOF ---$/)
    if (n >= MIN && !tagged)
      print fname ":" end ": a proof of " n " lines needs `-- --- PROOF ---` after its `:= by`" \
            " — wrap the statement if the line has no room"
    if (n < MIN && tagged)
      print fname ":" end ": the proof flag marks a proof of " n " lines — it is for " MIN " or more"
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

if [ "$status" -eq 0 ]; then
  printf 'conventions: %s files, all checks passed\n' "$(printf '%s\n' "$files" | wc -l | tr -d ' ')"
fi

exit "$status"

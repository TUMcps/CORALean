import CORALean.Examples.Oracle.Dispatch

/-!
# `lake exe oracle`: a JSON-lines float-set oracle for CORA.cpp

A persistent process: one JSON object per line on stdin, one line of `{"ok":true,
...}` or `{"ok":false,"error":"..."}` on stdout, flushed after each, echoing an
optional request `"id"` either way. Stateless -- every request carries every
operand -- and a malformed line answers with an error rather than exiting; the
process exits `0` at EOF. `Dispatch.respond` is the whole of it from here.

Every other protocol detail lives beside what it governs, not repeated here:
scalars, matrices, intervals, zonotopes in `Oracle/Codec.lean`; the `dtype`
forms and `roundTo`'s exact rounding in `Oracle/Dtype.lean`; `op` names and
routing in `Oracle/Dispatch.lean`; each op's own semantics in `Oracle/Ops/*.lean`.
The client is stateless and echoes values back: every scalar the oracle prints
also parses back as input, at the dtype it was printed for (`Codec.lean`'s
`ExactScalar`, `Dtype.lean`'s `showExact`). `experiments/oracle/README.md` is
the human-facing summary, pointing back here.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

open CORALean.Oracle
open CORALean.Bench (runOrUnknown)

/-- `line`, its trailing `\n` and, on Windows, `\r`, dropped -- `stdin.getLine`'s own shape,
mirrored from `IO.FS.Stream.lines`. -/
def stripNewline (line : String) : String :=
  if line.isEmpty then line
  else if line.back == '\n' then
    let line := line.dropEnd 1 |>.copy
    if !line.isEmpty && line.back == '\r' then line.dropEnd 1 |>.copy else line
  else line

/-- One line in, one line out, until `stdin.getLine` returns empty -- EOF, `Stream.getLine`'s
own convention, at which point `main` returns and the process exits `0`. -/
partial def loop (version : String) (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then pure () else
    stdout.putStrLn (respond version (stripNewline line)).compress
    stdout.flush
    loop version stdin stdout


-- =====================================  MAIN DEFINITION  ====================================== --

def main : IO Unit := do
  let version ← runOrUnknown "git" #["rev-parse", "--short", "HEAD"]
  loop version (← IO.getStdin) (← IO.getStdout)


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

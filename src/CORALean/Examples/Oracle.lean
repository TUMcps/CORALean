import CORALean.Examples.Oracle.Run

/-!
# `lake exe oracle`: a JSON-lines float-set oracle for CORA.cpp

A persistent process: one JSON object per line on stdin, one line of `{"ok":true, ...}` or
`{"ok":false,"error":"..."}` on stdout, flushed after each, echoing an optional request `"id"`.
Stateless, every request carrying every operand; a malformed line answers with an error rather than
exiting; the process exits `0` at EOF. `Dispatch.respond` is the whole of it. Protocol details live
beside what they govern: `Oracle/Codec.lean`, `Oracle/Dtype.lean` (`dtype` forms, `roundTo`),
`Oracle/Dispatch.lean` (`op` routing), `Oracle/Ops/*.lean`; `ping`'s `"version"`/`"dirty"` come
from `Oracle/GitInfo.lean`. `experiments/oracle/README.md` is the human-facing summary.

## Inputs
* none

## Output
* the process serves requests until end of input
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

open CORALean.Oracle


-- =====================================  MAIN DEFINITION  ====================================== --

def main : IO Unit := run sounds


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

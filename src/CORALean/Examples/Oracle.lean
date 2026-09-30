import CORALean.Examples.Oracle.Run

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
`ExactScalar`, `Dtype.lean`'s `showExact`). `ping`'s `"version"`/`"dirty"` are CORALean's own
commit and working-tree state, resolved from where the executable runs rather than the caller's
cwd (`Oracle/GitInfo.lean`), `"unknown"`/`false` when that cannot be told.
`experiments/oracle/README.md` is the human-facing summary, pointing back here.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

open CORALean.Oracle


-- =====================================  MAIN DEFINITION  ====================================== --

def main : IO Unit := run sounds


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

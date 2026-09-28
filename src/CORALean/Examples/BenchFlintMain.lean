import CORALean.Examples.BenchFlint

/-!
# `lake exe bench-flint`

The entry point alone, kept out of `Examples/BenchFlint.lean` (which holds
every other declaration) so that `scripts/check-axioms.lean` can import that
file without two top-level `main`s -- this one and `Examples/Bench.lean`'s --
landing in the same environment. `bench-flint <experiment> [--type flint]
[--format ...] [--config FILE] [--reps N] [--out DIR] [--exact]` runs like
`bench`; `bench-flint selftest` runs the differential test instead (README,
"FLINT backend (optional)").
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =====================================  MAIN DEFINITION  ====================================== --

def main (argv : List String) : IO Unit :=
  match CORALean.Bench.stripTypeFlint argv >>= CORALean.Bench.parseArgs with
  | .error e => do
    IO.eprintln s!"bench-flint: {e}"
    IO.Process.exit 1
  | .ok args => CORALean.Bench.dispatchFlint { args with ty := "flint" }


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

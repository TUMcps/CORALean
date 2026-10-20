import CORALean.Examples.Bench.FirstStepInput
import CORALean.Examples.Bench.Format

/-!
# `firststep`: a run's significand width

`prec` if the run gives one, else `format` through `formatToPrec`, else `53` -- `binary64`,
as `Registry.resolvedPrec` for `--prec`/`--format`.

## Inputs
* `run` – first-step run description

## Output
* significand width of the run
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- =====================================  MAIN DEFINITION  ====================================== --

def FirstStepRun.sigBits (run : FirstStepRun) : Nat :=
  match run.prec with
  | some p => p
  | none => match run.format with
    | some fmt => (formatToPrec fmt).toOption.getD 53
    | none => 53

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

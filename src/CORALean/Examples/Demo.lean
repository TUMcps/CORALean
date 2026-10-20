import CORALean.Examples.Demo.Binary64
import CORALean.Examples.Demo.Enclose
import CORALean.Examples.Demo.LinParamStep
import CORALean.Examples.Demo.Reach
import CORALean.Examples.Demo.Reduce

/-!
# Something that runs

Everything here is proved elsewhere; what is new is a number, which no `_outer` theorem supplies: a
theorem is as true of a box the size of the state space as of a tight one. The output is committed
as `scripts/demo-expected.txt` and `scripts/check-demo.sh` compares the two, so an enclosure that
silently widens fails the build. `Dyadic` is exact integer arithmetic, so the numbers do not depend
on the machine. `LinearSysDT.reach` runs at `Dyadic 24`, at the smaller
`Dyadic CORALean.Demo.smallP`, and at native `Float` (`Demo/Binary64.lean`); a network's `enclose`
and `reduceOnTheFly` run at `Dyadic 24`, and so does one `LinParamSys` step at an interval matrix
(`Demo/LinParamStep.lean`).

## Inputs
* none

## Output
* the demo reports are printed
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   02-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =====================================  MAIN DEFINITION  ====================================== --

def main : IO Unit := do
  IO.println (CORALean.Demo.reachReport 24)
  IO.println ""
  IO.println (CORALean.Demo.reachReport CORALean.Demo.smallP)
  IO.println ""
  IO.println CORALean.Demo.reachReportBinary64
  IO.println ""
  IO.println CORALean.Demo.encloseReport
  IO.println ""
  IO.println CORALean.Demo.reduceReport
  IO.println ""
  IO.println CORALean.Demo.paramReport


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.Examples.Demo.Binary64
import CORALean.Examples.Demo.Enclose
import CORALean.Examples.Demo.Reach
import CORALean.Examples.Demo.Reduce

/-!
# Something that runs

The first executable in this repository, and the first time any definition in it
has been evaluated. Everything here is proved elsewhere; what is new is a
*number*, which no `_outer` theorem supplies: a theorem is as true of a box the
size of the state space as of a tight one, and the only way to tell the two
apart is to compute one and look.

The output is committed as `scripts/demo-expected.txt` and `scripts/check-demo.sh`
compares the two, so an enclosure that silently widens fails the build. `Dyadic` is
exact integer arithmetic, so the numbers do not depend on the machine, the compiler
or the order of anything.

`LinearSysDT.reach` runs three times: at `Dyadic 24` and at the smaller
`Dyadic CORALean.Demo.smallP`, where 24 bits carries the whole run exactly and 8 does not,
and then at native `Float`, where the numbers do depend on the machine — see
`Demo/Binary64.lean` for what that run shows and what it assumes. A network's `enclose`,
and its on-the-fly reduction `reduceOnTheFly`, then run once each at `Dyadic 24`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

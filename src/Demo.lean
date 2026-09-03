import Demo.Propagate
import Demo.Reach

/-!
# Something that runs

The first executable in this repository, and the first time any definition in it
has been evaluated. Everything here is proved elsewhere; what is new is a
*number*, which no `_outer` theorem supplies: a theorem is as true of a box the
size of the state space as of a tight one, and the only way to tell the two
apart is to compute one and look.

The output is committed as `scripts/demo-expected.txt` and `scripts/check-demo.sh`
compares the two, so an enclosure that silently widens fails the build.

`Dyadic` is exact integer arithmetic, so the numbers do not depend on the
machine, the compiler or the order of anything.

`LinearSysDT.reach` runs twice, at `Dyadic 24` and at the smaller
`Dyadic Demo.smallP`: at 24 bits every product over the demo's horizon is
exact, so the error box a float zonotope carries never grows and directed
rounding is never exercised. The second run is where it is.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

def main : IO Unit := do
  IO.println (Demo.reachReport 24)
  IO.println ""
  IO.println (Demo.reachReport Demo.smallP)
  IO.println ""
  IO.println Demo.propagateReport

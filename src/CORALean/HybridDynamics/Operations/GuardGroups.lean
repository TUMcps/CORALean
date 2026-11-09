module

public import CORALean.HybridDynamics.Operations.GapRuns
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Sort

@[expose] public section

/-!
# `Location.guardGroups`

The grouping step of CORA's `@location/guardIntersect.m` (`aux_groupSets`): the hits
`(transition, set index)` of `potInt` are grouped by transition, the guards taken in increasing
order (MATLAB's `unique`), and every group is split where its set indices skip one
(`Location.gapRuns`), so that one group is one crossing of the guard. CORA's order is kept: of a
guard's runs all but the last go to the front of the list, each ahead of everything before it, and
the last stays behind them, in the order of the guards.

## Inputs
* `hits` – `(transition, set index)` pairs, in the order `potInt` returns them

## Output
* `(transition, set indices)` per crossing, the indices without gaps
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The crossings `(transition, set indices)` of the guards the hits name. -/
def Location.guardGroups (hits : List (ℕ × ℕ)) : List (ℕ × List ℕ) :=
  let guards := ((hits.map Prod.fst).dedup).mergeSort
  let runsOf := fun g => Location.gapRuns ((hits.filter fun h => h.1 = g).map Prod.snd)
  (guards.foldl (fun acc g => ((runsOf g).dropLast.reverse.map fun r => (g, r)) ++ acc) []) ++
    guards.filterMap fun g => ((runsOf g).getLast?).map fun r => (g, r)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.Global.Float.Interfaces

@[expose] public section

/-!
# The records of `HybridAutomaton.reachQueueFloat`

The options of CORA's `hybridAutomaton/reach` that the float definition reads (`Δt` per location,
`η`, `ρ`, the horizon, the location whose entry is not followed, `checkFlow`, the fuel), a set
waiting in the queue (CORA's `list`: `set`, `loc`, `time` as its two ends, `parent`), and a branch
of the reachable set (CORA's `reachSet` of one location, with the times its stay started at).
`checkFlow` drops the sets of a crossing whose flow points strictly into the invariant.

## Inputs
* `L` – location type
* `𝕋` – scalar type
* `n` – dimension

## Output
* the options, the queue entry and the branch
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- The step `Δt` of each location, the orders `η` and `ρ`, the final time, the location whose
entry is not followed (`params.finalLoc`), CORA's `checkFlow`, and the number of queue entries
`reachQueueFloat` analyses at most. -/
structure HybridReachOptions (L 𝕋 : Type) where
  Δt : L → 𝕋
  η : ℕ
  ρ : ℕ
  tFinal : ℚ
  finalLoc : L
  checkFlow : Bool
  fuel : ℕ

/-- A set waiting for its location: the set, the location, the lower and upper end of the time it
is entered at, and the branch that produced it. -/
structure HybridPending (L 𝕋 : Type) (n : ℕ) where
  loc : L
  set : Zonotope (Vec 𝕋 n)
  tlo : ℚ
  thi : ℚ
  parent : Option ℕ

/-- The time-interval sets of one stay, with the location, the producing branch and the times the
stay started at. -/
structure HybridBranch (L 𝕋 : Type) (n : ℕ) where
  loc : L
  parent : Option ℕ
  sets : List (Zonotope (Vec 𝕋 n))
  tlo : ℚ
  thi : ℚ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

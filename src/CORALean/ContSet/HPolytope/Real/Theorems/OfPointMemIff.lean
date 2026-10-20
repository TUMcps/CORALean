module

public import CORALean.ContSet.HPolytope.Real.Operations.OfPoint
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# `HPolytope.ofPoint` denotes exactly one point

The converse to `mem_ofPoint`: the `n` equality rows pin every coordinate.

## Inputs
* `v` – vector of length `n`
* `x` – point of length `n`

## Hypotheses
* none

## Conclusion
* `HPolytope.ofPoint` denotes exactly one point
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_ofPoint_iff (v x : Vec ℝ n) :
    x ∈ (HPolytope.ofPoint v).construct ↔ x = v := by -- --- PROOF ---
  constructor
  · rintro ⟨-, h⟩
    funext i
    exact h i
  · rintro rfl
    exact HPolytope.mem_ofPoint _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

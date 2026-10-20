module

public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem

@[expose] public section

/-!
# A generator-free zonotope contains nothing else

The converse to `mem_ofPoint`: no generator leaves no coefficient to spend, so
`ofPoint v` denotes `v` and nothing besides — read off `construct` directly, the
same unfolding `mem_ofPoint` needs a `show` for.

## Inputs
* `v` – point
* `x` – candidate point

## Hypotheses
* none

## Conclusion
* `x` lies in the point zonotope iff it equals `v`
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_ofPoint_iff (v x : α) :
    x ∈ (Zonotope.ofPoint v).construct ↔ x = v := by -- --- PROOF ---
  constructor
  · rintro ⟨β, -, hxeq⟩
    simpa only [Zonotope.ofPoint, Finset.univ_eq_empty, Finset.sum_empty, add_zero] using hxeq
  · rintro rfl
    exact Zonotope.mem_ofPoint _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

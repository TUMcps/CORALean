module

public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Theorems.BoxToSlackOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.IntersectionExact

@[expose] public section

/-!
# `HPolytope.intersection` encloses

With both boxes certified empty of error, the intersection is exact
(`HPolytope.intersection_exact`). Otherwise each operand's box is in its slacks
(`HPolytope.boxToSlack_outer`), whose result has the origin box and so is read at its nominal
part, and the stacked nominal rows are the two nominal parts' intersection
(`HPolytope.mem_stackRows_iff`).

## Inputs
* `P₁` – H-polytope
* `P₂` – H-polytope

## Hypotheses
* none

## Conclusion
* the intersection contains every point of both operands
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intersection contains every point of both operands. -/
theorem HPolytope.intersection_outer (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) :
    P₁.construct ∩ P₂.construct ⊆ (P₁.intersection P₂).construct := by -- --- PROOF ---
  rintro x ⟨hx₁, hx₂⟩
  by_cases hc : (P₁.isErrFree && P₂.isErrFree) = true
  · simp only [Bool.and_eq_true] at hc
    exact HPolytope.intersection_exact hc.1 hc.2 ▸ ⟨hx₁, hx₂⟩
  rw [HPolytope.intersection, if_neg hc]
  -- each half in its own slack-widened rows, read at the nominal part
  exact HPolytope.mem_stackRows_iff.mpr
    ⟨(HPolytope.mem_nominal_of_origin rfl).mp (HPolytope.boxToSlack_outer P₁ hx₁),
     (HPolytope.mem_nominal_of_origin rfl).mp (HPolytope.boxToSlack_outer P₂ hx₂)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

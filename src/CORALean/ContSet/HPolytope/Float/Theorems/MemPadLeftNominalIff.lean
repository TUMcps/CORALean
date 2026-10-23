module

public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.HPolytope.Float.Theorems.MulVecPadLeft

@[expose] public section

/-!
# Membership of a left-padded nominal part

The padded part reads the block it came from.

## Inputs
* `P` – float polytope
* `x` – point of the padded space

## Hypotheses
* none

## Conclusion
* the point lies in the padded nominal part iff its left block lies in the nominal part of `P`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Membership of the padded nominal part is membership of the block it came from. -/
theorem HPolytope.mem_padLeft_nominal_iff {P : HPolytope 𝕋 (Vec 𝕋 n₁)} {x : Vec ℝ (n₁ + n₂)} :
    x ∈ (P.padLeft n₂).nominal.construct ↔ blockLeft n₁ n₂ x ∈ P.nominal.construct := by
  rw [HPolytope.mem_nominal_iff, HPolytope.mem_nominal_iff]
  simp only [HPolytope.padLeft, HPolytope.mulVec_padLeft]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

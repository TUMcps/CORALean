module

public import CORALean.ContSet.HPolytope.Float.Operations.PadRight
public import CORALean.ContSet.HPolytope.Float.Theorems.MulVecPadRight

@[expose] public section

/-!
# Membership of a right-padded nominal part

The mirror of the left-padded statement for the right block.

## Inputs
* `P` – float polytope
* `x` – point of the padded space

## Hypotheses
* none

## Conclusion
* the point lies in the padded nominal part iff its right block lies in the nominal part of `P`
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

/-- The mirror statement for the right block. -/
theorem HPolytope.mem_padRight_nominal_iff {P : HPolytope 𝕋 (Vec 𝕋 n₂)} {x : Vec ℝ (n₁ + n₂)} :
    x ∈ (HPolytope.padRight n₁ P).nominal.construct ↔ blockRight n₁ n₂ x ∈ P.nominal.construct := by
  rw [HPolytope.mem_nominal_iff, HPolytope.mem_nominal_iff]
  simp only [HPolytope.padRight, HPolytope.mulVec_padRight]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

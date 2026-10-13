import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadRight

/-!
# Membership in `HPolytope.padRight`

The mirror statement for the right block.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- the mirror statement for the right block
theorem HPolytope.mem_padRight_iff {P : HPolytope 𝕋 (Vec 𝕋 n₂)} {x : Vec ℝ (n₁ + n₂)} :
    x ∈ (HPolytope.padRight n₁ P).construct
      ↔ blockRight n₁ n₂ x ∈ P.construct := by -- --- PROOF ---
  constructor
  · intro h
    obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp h
    refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
    · have hh := hle i
      simp only [HPolytope.padRight, HPolytope.mulVec_padRight] at hh
      exact hh
    · have hh := heq i
      simp only [HPolytope.padRight, HPolytope.mulVec_padRight] at hh
      exact hh
  · intro h
    obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp h
    refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
    · simp only [HPolytope.padRight, HPolytope.mulVec_padRight]
      exact hle i
    · simp only [HPolytope.padRight, HPolytope.mulVec_padRight]
      exact heq i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

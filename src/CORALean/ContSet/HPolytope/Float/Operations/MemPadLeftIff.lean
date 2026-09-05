import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadLeft

/-!
# Membership in `HPolytope.padLeft`

Membership of the padded polytope is membership of the block it came from,
both ways.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}

-- so membership of the padded polytope is membership of that block, both ways
theorem HPolytope.mem_padLeft_iff {P : HPolytope 𝕋 n₁} {x : Vec ℝ (n₁ + n₂)} :
    x ∈ (P.padLeft n₂).construct ↔ blockLeft n₁ n₂ x ∈ P.construct := by
  constructor
  · intro h
    obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp h
    refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
    · have hh := hle i
      simp only [HPolytope.padLeft, HPolytope.mulVec_padLeft] at hh
      exact hh
    · have hh := heq i
      simp only [HPolytope.padLeft, HPolytope.mulVec_padLeft] at hh
      exact hh
  · intro h
    obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp h
    refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
    · simp only [HPolytope.padLeft, HPolytope.mulVec_padLeft]
      exact hle i
    · simp only [HPolytope.padLeft, HPolytope.mulVec_padLeft]
      exact heq i

end CORALean.Float

module

public import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff

@[expose] public section

/-!
# `HPolytope.intersection` is exact, over a floating-point scalar

The constraint lists concatenate. Nothing is computed, so nothing rounds.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.intersection_exact (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) :
    P₁.construct ∩ P₂.construct = (P₁.intersection P₂).construct :=
  Set.ext fun _ => HPolytope.mem_intersection_iff.symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.HPolytope.Float.Operations.MemAndIff

/-!
# `HPolytope.and` is exact, over a floating-point scalar

The constraint lists concatenate. Nothing is computed, so nothing rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.and_exact (P₁ P₂ : HPolytope 𝕋 n) :
    P₁.construct ∩ P₂.construct = (P₁.and P₂).construct :=
  Set.ext fun _ => HPolytope.mem_and_iff.symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

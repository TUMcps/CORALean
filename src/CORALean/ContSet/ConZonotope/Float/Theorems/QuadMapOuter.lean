import CORALean.ContSet.ConZonotope.Float.Operations.QuadMap
import CORALean.ContSet.ConZonotope.Float.Theorems.DependentNominal
import CORALean.ContSet.ConZonotope.Float.Theorems.QuadMapDepNominal

/-!
# `ConZonotope.quadMap` over-approximates the quadratic map, on the factors

Every point of the operand, box included, is a point of the nominal set of `dependent`
(`dependent_nominal`), whose quadratic image is held by `quadMapDep` (`quadMapDep_nominal`). The
result keeps the operand's constraints on the first block of coefficients and gives the squares and
the products none, so it is an outer approximation: it contains the image, and need not equal it.
Unlike `Zonotope.quadMap_outer` the guarantee is about the constrained set, not a zonotope's.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.quadMap_outer (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    (fun x : Vec ℝ n => fun i => x ⬝ᵥ (toRealMat (Q i) *ᵥ x)) '' cZ.construct
      ⊆ (cZ.quadMap Q).construct := by
  rintro _ ⟨x, hx, rfl⟩
  exact ConZonotope.quadMapDep_nominal Q cZ.dependent
    ⟨x, ConZonotope.dependent_nominal cZ hx, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Float.Operations.ExtE

/-!
# The exponent matrix of `mul`, over a floating-point scalar

Split out of `Mul.lean` (issue #62): read again by `Theorems/EvalPolyOuter.lean`
and `Theorems/MulOuter.lean`, both outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The image's exponent column, the two columns added. Over ℕ, so exact. -/
def PolyZonotope.mulE (S₁ S₂ : PolyZonotope 𝕋 n) (hp : S₁.p = S₂.p) :
    Fin S₁.p → Fin ((S₁.h + 1) * (S₂.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE S₁ k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE S₂ (Fin.cast hp k) (finProdFinEquiv.symm l).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

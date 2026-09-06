import CORALean.ContSet.PolyZonotope.Real.Operations.ExtE

/-!
# The exponent matrix of `mul`

Split out of `Mul.lean` (issue #62): read again by the float layer's own
`Operations/Mul.lean`, `Theorems/EvalPolyOuter.lean`, `Theorems/MulOuter.lean`
and `Theorems/MulPoint.lean`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Its exponent column, the two columns added, `S₂`'s read at `S₁`'s factor
indices. -/
def PolyZonotope.mulE (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p) :
    Fin S₁.p → Fin ((S₁.h + 1) * (S₂.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE S₁ k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE S₂ (Fin.cast hp k) (finProdFinEquiv.symm l).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Real.Operations.ExtE

/-!
# The exponent matrix of `bilin`

One column per pair of extended columns, the two added: sound only because the
two sets share their factors, and the reason the result is a polynomial
zonotope again rather than an enclosure of one.

Nothing here reads the ambient types, so the exponent arithmetic of a product
is the same whatever the two sets hold — `mulE` is this at `Vec`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Its exponent column, the two columns added, `S₂`'s read at `S₁`'s factor
indices. -/
def PolyZonotope.bilinE (S₁ : PolyZonotope α) (S₂ : PolyZonotope β) (hp : S₁.p = S₂.p) :
    Fin S₁.p → Fin ((S₁.h + 1) * (S₂.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE S₁ k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE S₂ (Fin.cast hp k) (finProdFinEquiv.symm l).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

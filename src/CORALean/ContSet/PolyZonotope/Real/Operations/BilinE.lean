module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ExtE
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# The exponent matrix of `bilin`

One column per pair of extended columns, the two added: sound only because the
two sets share their factors, and the reason the result is a polynomial
zonotope again rather than an enclosure of one.

Nothing here reads the ambient types, so the exponent arithmetic of a product
is the same whatever the two sets hold — `mulE` is this at `Vec`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Its exponent column, the two columns added, `pZ₂`'s read at `pZ₁`'s factor
indices. -/
def PolyZonotope.bilinE (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β) (hp : pZ₁.p = pZ₂.p) :
    Fin pZ₁.p → Fin ((pZ₁.h + 1) * (pZ₂.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE pZ₁ k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE pZ₂ (Fin.cast hp k) (finProdFinEquiv.symm l).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

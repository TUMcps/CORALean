import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The independent generators of `bilinOuter`

CORA's `matMap` keeps what `bilin` drops: each independent generator of one set paired with
every generator of the other, centre included, and the dependent generators of one with the
independent ones of the other. The three blocks, in this order: independent of the first with
the extended generators of the second, independent with independent, extended generators of the
first with the independent ones of the second. (CORA lists the same pairs as five blocks.)
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pairs `f (GI₁ j) (ext₂ l)`, `f (GI₁ j) (GI₂ l)`, `f (ext₁ l) (GI₂ j)` as one list. -/
def PolyZonotope.bilinGI (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β) :
    Fin (pZ₁.q * (pZ₂.h + 1) + pZ₁.q * pZ₂.q + (pZ₁.h + 1) * pZ₂.q) → γ :=
  Fin.append
    (Fin.append
      (fun l => f (pZ₁.GI (finProdFinEquiv.symm l).1) (pZ₂.extG (finProdFinEquiv.symm l).2))
      (fun l => f (pZ₁.GI (finProdFinEquiv.symm l).1) (pZ₂.GI (finProdFinEquiv.symm l).2)))
    (fun l => f (pZ₁.extG (finProdFinEquiv.symm l).1) (pZ₂.GI (finProdFinEquiv.symm l).2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Real.Operations.MatMap
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinOuterMem

/-!
# `matMap` encloses the matrix product at shared factors

Outer, not exact: the independent cross terms are carried as independent generators, whose
coefficients (a product of a monomial and an independent coefficient, or of two independent ones)
range over a box and not independently of the factors.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n k m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.matMap_outer (pZ₁ : PolyZonotope (Mat ℝ n k)) (pZ₂ : PolyZonotope (Mat ℝ k m))
    (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ) (ha : ∀ i, |a i| ≤ 1) (β₁ : Fin pZ₁.q → ℝ)
    (β₂ : Fin pZ₂.q → ℝ) (hβ₁ : ∀ j, |β₁ j| ≤ 1) (hβ₂ : ∀ j, |β₂ j| ≤ 1) :
    (pZ₁.point a + ∑ j, β₁ j • pZ₁.GI j) *
        (pZ₂.point (fun i => a (Fin.cast hp.symm i)) + ∑ j, β₂ j • pZ₂.GI j)
      ∈ (pZ₁.matMap pZ₂ hp).construct :=
  PolyZonotope.bilinOuter_mem matMulBilin pZ₁ pZ₂ hp a ha β₁ β₂ hβ₁ hβ₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

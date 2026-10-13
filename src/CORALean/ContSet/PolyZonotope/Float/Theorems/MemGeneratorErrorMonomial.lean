import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne

/-!
# Generator error at the dependent block, where coefficients are monomials

`|∏ₖ αₖ^Eₖᵢ| ≤ 1` is what a zonotope's free coefficient satisfies, so a rounded
dependent generator costs one `radius` of entrywise error, independent of the
factor count and degree.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same at the dependent block, where the coefficients are monomials. -/
theorem PolyZonotope.mem_generatorError_monomial {G : Mat 𝕋 n h} {Δ : Mat ℝ n h}
    {E : Fin p → Fin h → ℕ} {a : Fin p → ℝ}
    (hG : ∀ i l, |Δ i l| ≤ toReal (G i l)) (ha : ∀ k, |a k| ≤ 1) :
    (fun i => ∑ l, Δ i l * Real.PolyZonotope.monomial E a l)
      ∈ (PolyZonotope.generatorError G).construct :=
  PolyZonotope.mem_generatorError hG fun l => Real.PolyZonotope.abs_monomial_le_one E ha l

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

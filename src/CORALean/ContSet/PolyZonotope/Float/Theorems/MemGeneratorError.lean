import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne

/-!
# What a monomial costs the float layer

A zonotope scales a generator by one coefficient, a polynomial zonotope by
`∏ₖ αₖ^Eₖᵢ`. A product of `p` rounded powers would accumulate rounding as a
single multiplication does not, and the bound would grow with the total degree.

None of that is paid, because **no monomial is ever computed**. `αₖ` is a
coefficient the *set* quantifies over, not a value the implementation holds, so
the monomial is an exact real in every one of `plus`, `mtimes` and `quadMap`.
What the float layer stores of a monomial is its exponent column, over ℕ, and
every operation on exponents is exact there, so the nominal set's monomials are
the exact layer's and not roundings of them.

The monomial therefore enters through one fact and no other: `|∏ₖ αₖ^Eₖᵢ| ≤ 1`,
which is what a zonotope's free coefficient satisfies, so a rounded dependent
generator costs one `radius` of entrywise error, independent of `p` and degree.
The cost is in the *count*: `quadMap` sums `(h+1)²` errors per coordinate where
`mtimes` sums `h`, which is why `compact` is worth running before, not after.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p h : ℕ}

/-- Entrywise generator error scaled by any coefficients in `[-1,1]`. -/
theorem PolyZonotope.mem_generatorError {G : Mat 𝕋 n h} {Δ : Mat ℝ n h} {t : Vec ℝ h}
    (hG : ∀ i l, |Δ i l| ≤ toReal (G i l)) (ht : ∀ l, |t l| ≤ 1) :
    (fun i => ∑ l, Δ i l * t l) ∈ (PolyZonotope.generatorError G).construct := by
  intro i
  have key := abs_sum_le_radius (fun i l => le_trans (hG i l) (le_abs_self _)) ht i
  refine ⟨?_, le_of_abs_le key⟩
  show toReal (neg (radius G i)) ≤ ∑ l, Δ i l * t l
  rw [toReal_neg]
  exact neg_le_of_abs_le key

/-- The same at the dependent block, where the coefficients are monomials. -/
theorem PolyZonotope.mem_generatorError_monomial {G : Mat 𝕋 n h} {Δ : Mat ℝ n h}
    {E : Fin p → Fin h → ℕ} {a : Fin p → ℝ}
    (hG : ∀ i l, |Δ i l| ≤ toReal (G i l)) (ha : ∀ k, |a k| ≤ 1) :
    (fun i => ∑ l, Δ i l * Real.PolyZonotope.monomial E a l)
      ∈ (PolyZonotope.generatorError G).construct :=
  PolyZonotope.mem_generatorError hG fun l => Real.PolyZonotope.abs_monomial_le_one E ha l

end CORALean.Float

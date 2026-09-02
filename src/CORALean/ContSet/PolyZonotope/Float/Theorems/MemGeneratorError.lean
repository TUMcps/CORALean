import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

/-!
# What a monomial costs the float layer

The question the representation raises: a zonotope scales a generator by one
coefficient, a polynomial zonotope by `∏ₖ αₖ^Eₖᵢ`. A product of `p` rounded
powers would accumulate rounding the way a single multiplication does not, and
the bound would have to be `(1+ε)^{∑ₖ Eₖᵢ}` or worse — growing with the total
degree, and needing a relative-error model this layer deliberately does not
assume.

None of that is paid, because **no monomial is ever computed**. `αₖ` is a
coefficient the *set* quantifies over, not a value the implementation holds: the
denoted set ranges over every admissible `α`, so the monomial is an exact real
in every one of `plus`, `mtimes` and `quadMap`. What the float layer stores of a
monomial is its exponent column, over ℕ, and every operation on exponents —
`plusE`'s block-diagonal append, `quadMapE`'s column addition, dropping a column
or a factor — is exact in ℕ. So the nominal set's monomials are the exact
layer's monomials and not roundings of them.

The monomial therefore enters here through one fact and no other:
`|∏ₖ αₖ^Eₖᵢ| ≤ 1`, which is exactly what a zonotope's free coefficient
satisfies. `abs_sum_le_radius` needs nothing more, so a rounded dependent
generator costs precisely what a rounded zonotope generator costs — one `radius`
of the entrywise error, independent of `p` and of the degree.

The cost is in the *count* of generators rather than in the size of each. A
zonotope's `mtimes` sums `h` errors per coordinate; `quadMap` sums `(h+1)²`,
which is where a polynomial zonotope's rounding actually accumulates, and why
`compact` is worth running before rather than after.

The `_monomial` form is the general one specialised, so a caller reading the
statement at a dependent block never has to produce the bound itself.
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

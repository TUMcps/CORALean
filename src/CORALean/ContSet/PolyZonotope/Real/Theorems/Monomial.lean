import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# What a monomial in the factors satisfies

Three facts about `PolyZonotope.monomial`, which `construct` is stated with and
which therefore stays beside the structure. Each is three lines, each is about
that one definition, and no operation uses one without the others, so they share
a file rather than each taking one.

The bound is what lets a dependent generator be read as an independent one, so
every enclosing conversion out of this representation rests on it; the zero and
the sum are what a concatenation and a quadratic map do to an exponent column.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- A monomial never leaves `[-1,1]`, which is what lets every dependent
generator be read as an independent one. -/
theorem PolyZonotope.abs_monomial_le_one {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) (i : Fin h) :
    |PolyZonotope.monomial E a i| ≤ 1 := by
  rw [PolyZonotope.monomial, Finset.abs_prod]
  refine Finset.prod_le_one (fun k _ => abs_nonneg _) fun k _ => ?_
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (ha k)

/-- Every factor at exponent zero, so the monomial is `1`: the shape a
concatenation gives the generators it did not come from. -/
theorem PolyZonotope.monomial_zero {p h : ℕ} {E : Fin p → Fin h → ℕ} (a : Fin p → ℝ)
    {i : Fin h} (hE : ∀ k, E k i = 0) : PolyZonotope.monomial E a i = 1 := by
  rw [PolyZonotope.monomial]
  exact Finset.prod_eq_one fun k _ => by rw [hE k, pow_zero]

/-- Exponent columns add where monomials multiply, which is what keeps the
representation closed under a quadratic map. -/
theorem PolyZonotope.monomial_add {p h : ℕ} (E₁ E₂ : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (i : Fin h) :
    PolyZonotope.monomial (fun k i => E₁ k i + E₂ k i) a i
      = PolyZonotope.monomial E₁ a i * PolyZonotope.monomial E₂ a i := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial, PolyZonotope.monomial,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => pow_add (a k) (E₁ k i) (E₂ k i)

end CORALean.Real

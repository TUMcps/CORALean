import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLe

/-!
# Two monomials that agree off one even factor drift only downwards

What turns the exponent relaxation's error interval one-sided, and so what makes
a centre shift worth taking. `abs_sub_monomial_le` bounds the drift by `eDiff`
symmetrically; here it is also signed, so the drift runs over `[-ξ_E, 0]` and
half of it is a constant the centre can absorb.

Three hypotheses carry it. Every exponent of column `i` even makes the shared
factors a product of even powers, hence nonnegative; `E_{k₀,j}` even makes both
powers at `k₀` powers of `α²`, which lies in `[0,1]`; and `E_{k₀,j} ≤ E_{k₀,i}`
then orders them, a higher power of a number in `[0,1]` being the smaller. The
second is the hypothesis `[1, Thm. 2]` omits, and without it `α^{E_{k₀,j}}`
changes sign and nothing is one-sided.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- Two monomials whose columns agree off `k₀`, with column `i` even, `E_{k₀,j}`
even and `E_{k₀,j} ≤ E_{k₀,i}`, drift in one direction only. -/
theorem PolyZonotope.sub_monomial_nonpos {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) {i j : Fin h} {k₀ : Fin p}
    (hsim : ∀ k, k ≠ k₀ → E k i = E k j) (heven : ∀ k, Even (E k i))
    (hevenj : Even (E k₀ j)) (hle : E k₀ j ≤ E k₀ i) :
    PolyZonotope.monomial E a i - PolyZonotope.monomial E a j ≤ 0 := by
  -- both monomials split at `k₀`, and everything off `k₀` is shared
  have hsplit : ∀ l : Fin h, PolyZonotope.monomial E a l
      = a k₀ ^ E k₀ l * ∏ k ∈ Finset.univ.erase k₀, a k ^ E k l :=
    fun l => (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀)).symm
  have hrest : ∏ k ∈ Finset.univ.erase k₀, a k ^ E k i
      = ∏ k ∈ Finset.univ.erase k₀, a k ^ E k j :=
    Finset.prod_congr rfl fun k hk => by rw [hsim k (Finset.ne_of_mem_erase hk)]
  -- the shared factors are even powers, so the product they form is nonnegative
  have hR : 0 ≤ ∏ k ∈ Finset.univ.erase k₀, a k ^ E k j :=
    Finset.prod_nonneg fun k hk => by
      rw [← hsim k (Finset.ne_of_mem_erase hk)]
      exact (heven k).pow_nonneg (a k)
  obtain ⟨s, hs⟩ := heven k₀
  obtain ⟨t, ht⟩ := hevenj
  -- `α²` is what both powers at `k₀` are powers of, and it stays in `[0,1]`
  have hy1 : a k₀ ^ 2 ≤ 1 := by
    have h : |a k₀| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) (ha k₀)
    rwa [← abs_pow, abs_of_nonneg (sq_nonneg _)] at h
  have hts : t ≤ s := by omega
  -- the higher power of a number in `[0,1]` is the smaller one
  have hd : a k₀ ^ E k₀ i - a k₀ ^ E k₀ j ≤ 0 := by
    have hpow : (a k₀ ^ 2) ^ s ≤ (a k₀ ^ 2) ^ t :=
      pow_le_pow_of_le_one (sq_nonneg _) hy1 hts
    rw [hs, ht, ← two_mul, ← two_mul, pow_mul, pow_mul]
    linarith
  rw [hsplit i, hsplit j, hrest, ← sub_mul]
  -- nonpositive times nonnegative
  have hmul := mul_nonneg (neg_nonneg.mpr hd) hR
  rw [neg_mul] at hmul
  linarith

end CORALean.Real

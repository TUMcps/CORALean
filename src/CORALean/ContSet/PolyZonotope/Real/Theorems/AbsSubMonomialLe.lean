import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubPowLeEDiff

/-!
# Two monomials that agree off one factor drift by at most `eDiff`

What the exponent relaxation costs, in one line: the two monomials share every
factor but the one at `k₀`, so their difference is `(a_{k₀}^{E_i} - a_{k₀}^{E_j})`
times a product of powers of factors in `[-1,1]`, which never leaves `[-1,1]`
itself. `abs_sub_pow_le_eDiff` bounds the first, so `eDiff` bounds the whole.

Stated over a bare exponent matrix rather than over a set, so both layers read
it: the float layer stores its exponents over ℕ and its monomials are these.

The hypothesis is agreement off `k₀`, which is `[1, Def. 4]` minus the demand
that the columns actually differ there — nothing here needs them to.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two monomials whose exponent columns agree off `k₀` differ by at most
`eDiff` there: every other factor is shared and stays in `[-1,1]`. -/
theorem PolyZonotope.abs_sub_monomial_le {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) {i j : Fin h} {k₀ : Fin p}
    (hsim : ∀ k, k ≠ k₀ → E k i = E k j) :
    |PolyZonotope.monomial E a i - PolyZonotope.monomial E a j|
      ≤ (PolyZonotope.eDiff (E k₀ i) (E k₀ j) : ℝ) := by -- --- PROOF ---
  have hsplit : ∀ l : Fin h, PolyZonotope.monomial E a l
      = a k₀ ^ E k₀ l * ∏ k ∈ Finset.univ.erase k₀, a k ^ E k l :=
    fun l => (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀)).symm
  have hrest : ∏ k ∈ Finset.univ.erase k₀, a k ^ E k i
      = ∏ k ∈ Finset.univ.erase k₀, a k ^ E k j :=
    Finset.prod_congr rfl fun k hk => by rw [hsim k (Finset.ne_of_mem_erase hk)]
  -- the shared factors, which no relaxation touches
  have hle : |∏ k ∈ Finset.univ.erase k₀, a k ^ E k j| ≤ 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_one (fun k _ => abs_nonneg _) fun k _ => ?_
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (ha k)
  have hpow := PolyZonotope.abs_sub_pow_le_eDiff (ha k₀) (E k₀ i) (E k₀ j)
  rw [hsplit i, hsplit j, hrest, ← sub_mul, abs_mul]
  calc |a k₀ ^ E k₀ i - a k₀ ^ E k₀ j| * |∏ k ∈ Finset.univ.erase k₀, a k ^ E k j|
      ≤ (PolyZonotope.eDiff (E k₀ i) (E k₀ j) : ℝ) * 1 :=
        mul_le_mul hpow hle (abs_nonneg _) (le_trans (abs_nonneg _) hpow)
    _ = (PolyZonotope.eDiff (E k₀ i) (E k₀ j) : ℝ) := mul_one _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

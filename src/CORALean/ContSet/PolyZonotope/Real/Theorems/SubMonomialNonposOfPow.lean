import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# A signed power difference carries its sign to the whole monomial

What turns one-sidedness at a single factor into one-sidedness of the drift.
Two monomials agreeing off `k₀` are the same product of shared factors times
`α_{k₀}^{E_{k₀,i}}` and `α_{k₀}^{E_{k₀,j}}`, so their difference is that product
times the power difference. Every exponent off `k₀` being even makes the product
nonnegative, and then the power difference alone decides the sign.

Split from the power fact and from `eDrift`'s case analysis so that each side is
stated where it is proved: this asks nothing about `[-1,1]` and nothing about
parity at `k₀`, only that the shared factors cannot turn the sign around. It is
the half of `[1, Thm. 1]`'s halving that the exponent matrix decides.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two monomials agreeing off `k₀`, with every exponent there even, drift with
the sign their powers at `k₀` drift with. -/
theorem PolyZonotope.sub_monomial_nonpos_of_pow {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} {i j : Fin h} {k₀ : Fin p} (hsim : ∀ k, k ≠ k₀ → E k i = E k j)
    (heven : ∀ k, k ≠ k₀ → Even (E k i)) (hd : a k₀ ^ E k₀ i - a k₀ ^ E k₀ j ≤ 0) :
    PolyZonotope.monomial E a i - PolyZonotope.monomial E a j ≤ 0 := by -- --- PROOF ---
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
      exact (heven k (Finset.ne_of_mem_erase hk)).pow_nonneg (a k)
  rw [hsplit i, hsplit j, hrest, ← sub_mul]
  -- nonpositive times nonnegative
  have hmul := mul_nonneg (neg_nonneg.mpr hd) hR
  rw [neg_mul] at hmul
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

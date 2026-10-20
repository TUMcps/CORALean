module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

@[expose] public section

/-!
# A signed power difference carries its sign to the whole monomial

What turns one-sidedness at a single factor into one-sidedness of the drift. Two monomials
agreeing off `k₀` are the same product of shared factors times `α_{k₀}^{E_{k₀,i}}` and
`α_{k₀}^{E_{k₀,j}}`, so their difference is that product times the power difference. Every
exponent off `k₀` being even makes the product nonnegative, and then the power difference
alone decides the sign. This is the half of `[1, Thm. 1]`'s halving the exponent matrix decides.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `a` – factor values
* `i` – first generator index
* `j` – second generator index
* `k₀` – factor index

## Hypotheses
* `hsim` – exponents agree outside that factor
* `heven` – first generator has even exponents elsewhere
* `hd` – power difference in that factor is nonpositive

## Conclusion
* the first monomial does not exceed the second

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.SubMonomialNonposOfPow
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SubPowNonpos

@[expose] public section

/-!
# Two monomials that agree off one even factor drift only downwards

The all-even case of `[1, Thm. 1]`, and the shape of drift that makes a center
shift worth taking: `abs_sub_monomial_le` bounds the drift by `eDiff`
symmetrically, and this signs it, so the drift runs over `[-ξ_E, 0]` and half of
it is a constant the center can absorb.

Two facts assembled. Every exponent of column `i` being even makes the shared
factors a product of even powers, which is `sub_monomial_nonpos_of_pow`'s
hypothesis; both exponents at `k₀` even and ordered is `sub_pow_nonpos`'s second
disjunct. The evenness of `E_{k₀,j}` is what `[1, Thm. 1]` omits, and without it
`α^{E_{k₀,j}}` changes sign and nothing is one-sided.

Kept as its own statement because this is the case `[1]` names; `eDrift` reads
the same two facts at their full generality, where a zero exponent is one-sided
at any parity.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two monomials whose columns agree off `k₀`, with column `i` even, `E_{k₀,j}`
even and `E_{k₀,j} ≤ E_{k₀,i}`, drift in one direction only. -/
theorem PolyZonotope.sub_monomial_nonpos {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) {i j : Fin h} {k₀ : Fin p}
    (hsim : ∀ k, k ≠ k₀ → E k i = E k j) (heven : ∀ k, Even (E k i))
    (hevenj : Even (E k₀ j)) (hle : E k₀ j ≤ E k₀ i) : -- --- STMT ---
    PolyZonotope.monomial E a i - PolyZonotope.monomial E a j ≤ 0 :=
  -- both exponents at `k₀` even and ordered is the second disjunct of the sign fact
  PolyZonotope.sub_monomial_nonpos_of_pow E hsim (fun k _ => heven k)
    (PolyZonotope.sub_pow_nonpos (ha k₀) (Or.inr ⟨heven k₀, hevenj, hle⟩))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

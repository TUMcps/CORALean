module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDrift
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLe
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SubMonomialNonposOfPow
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SubPowNonpos

@[expose] public section

/-!
# `eDrift` brackets the drift of one monomial from another

The two-sided reading of `[1, Prop. 3]`: `abs_sub_monomial_le` says the drift of
two monomials agreeing off `k₀` stays within `ξ_E` of zero, and this says which
half of that interval it can actually reach. Where a sign never changes the
opposite reach is `0`, and a relaxation can then put the interval's midpoint in
its centre and only its half-width in a generator.

One hypothesis, the agreement off `k₀`, and no evenness: `eDrift` reads the
parity out of the exponent matrix itself, so the caller is never asked for it
and a pair with nothing to exploit falls back on the symmetric bound.

`sub_monomial_nonpos` is the case where the reach upward vanishes and every
exponent of column `i` is even. The upward branch is the same argument with the
two columns exchanged, which is why the bracket is symmetric under swapping them.

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

/-- The drift of the monomial at `i` from the one at `j`, for columns agreeing
off `k₀`, lies in `[-fst, snd]` of `eDrift`. -/
theorem PolyZonotope.sub_monomial_mem_eDrift {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) {i j : Fin h} {k₀ : Fin p}
    (hsim : ∀ k, k ≠ k₀ → E k i = E k j) :
    PolyZonotope.monomial E a i - PolyZonotope.monomial E a j
      ∈ Set.Icc (-((PolyZonotope.eDrift E k₀ i j).1 : ℝ))
        ((PolyZonotope.eDrift E k₀ i j).2 : ℝ) := by -- --- PROOF ---
  have habs := abs_le.mp (PolyZonotope.abs_sub_monomial_le E ha hsim)
  rw [Set.mem_Icc, PolyZonotope.eDrift]
  split_ifs with hcol hdown hup
  -- the shared factors are nonnegative, so the sign at `k₀` decides the drift's
  · have heven : ∀ k, k ≠ k₀ → Even (E k i) := fun k hk => Nat.even_iff.mpr (hcol k hk)
    have hcase : E k₀ j = 0 ∨ (Even (E k₀ i) ∧ Even (E k₀ j) ∧ E k₀ j ≤ E k₀ i) := by
      rcases hdown with hz | ⟨hi, hj, hle⟩
      · exact Or.inl hz
      · exact Or.inr ⟨Nat.even_iff.mpr hi, Nat.even_iff.mpr hj, hle⟩
    refine ⟨habs.1, ?_⟩
    rw [Nat.cast_zero]
    exact PolyZonotope.sub_monomial_nonpos_of_pow E hsim heven
      (PolyZonotope.sub_pow_nonpos (ha k₀) hcase)
  -- the same with the two columns exchanged, which reverses the drift
  · have heven : ∀ k, k ≠ k₀ → Even (E k j) := fun k hk => by
      rw [← hsim k hk]
      exact Nat.even_iff.mpr (hcol k hk)
    have hcase : E k₀ i = 0 ∨ (Even (E k₀ j) ∧ Even (E k₀ i) ∧ E k₀ i ≤ E k₀ j) := by
      rcases hup with hz | ⟨hi, hj, hle⟩
      · exact Or.inl hz
      · exact Or.inr ⟨Nat.even_iff.mpr hj, Nat.even_iff.mpr hi, hle⟩
    have hrev := PolyZonotope.sub_monomial_nonpos_of_pow E (fun k hk => (hsim k hk).symm) heven
      (PolyZonotope.sub_pow_nonpos (ha k₀) hcase)
    refine ⟨?_, habs.2⟩
    rw [Nat.cast_zero, neg_zero]
    linarith
  -- nothing to exploit: the symmetric bound is all there is
  · exact ⟨habs.1, habs.2⟩
  · exact ⟨habs.1, habs.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

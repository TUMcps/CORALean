module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLe
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# Two monomials drift by at most the sum of their `eDiff`s

`[1, Prop. 4]`, and the whole of it. The chain of zero-length generators the paper inserts is
a chain of *hybrid* monomials here (column `i` off a finset and column `j` on it), so no
intermediate polynomial zonotope is built. Each step moves the exponent at one index, which
`abs_sub_monomial_le` bounds, and the triangle inequality telescopes. Nothing relates the two
columns: `eDiff a a = 0`, so the sum over every factor is the paper's sum over the indices
where they differ. Similarity (`[1, Def. 4]`) buys precision here rather than soundness.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `a` – factor values
* `i` – first generator index
* `j` – second generator index

## Hypotheses
* `ha` – factor values are at most one

## Conclusion
* the monomials differ by at most the summed exponent differences

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One step of the chain, at bare exponent vectors: two products that agree off
`k₀` are two columns of a two-column matrix. -/
theorem PolyZonotope.aux_abs_sub_prod_le {p : ℕ} {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1)
    (A B : Fin p → ℕ) {k₀ : Fin p} (hsim : ∀ k, k ≠ k₀ → A k = B k) :
    |(∏ k, a k ^ A k) - ∏ k, a k ^ B k| ≤ (PolyZonotope.eDiff (A k₀) (B k₀) : ℝ) :=
  PolyZonotope.abs_sub_monomial_le (fun k => ![A k, B k]) ha (i := 0) (j := 1) hsim

/-- The hybrid that reads column `j` on `s` and column `i` off it is within the
`eDiff`s of `s` of the monomial at `i`. -/
theorem PolyZonotope.aux_abs_sub_hybrid_le {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) (i j : Fin h) (s : Finset (Fin p)) :
    |PolyZonotope.monomial E a i - ∏ k, a k ^ (if k ∈ s then E k j else E k i)|
      ≤ ∑ k ∈ s, (PolyZonotope.eDiff (E k i) (E k j) : ℝ) := by -- --- PROOF ---
  induction s using Finset.induction_on with
  | empty =>
    -- nothing has moved yet, so the hybrid is the monomial at `i` itself
    have h0 : ∀ k, (if k ∈ (∅ : Finset (Fin p)) then E k j else E k i) = E k i :=
      fun k => if_neg (Finset.notMem_empty k)
    simp only [h0, Finset.sum_empty]
    rw [show (∏ k, a k ^ E k i) = PolyZonotope.monomial E a i from rfl, sub_self, abs_zero]
  | insert k₀ s hk₀ ih =>
    -- the step from `s` to `insert k₀ s` moves the exponent at `k₀` alone
    have hsim : ∀ k, k ≠ k₀ → (if k ∈ s then E k j else E k i)
        = if k ∈ insert k₀ s then E k j else E k i := by
      intro k hk
      have hmem : k ∈ insert k₀ s ↔ k ∈ s := by
        rw [Finset.mem_insert]
        exact ⟨fun h => h.resolve_left hk, Or.inr⟩
      simp only [hmem]
    have hstep := PolyZonotope.aux_abs_sub_prod_le ha
      (fun k => if k ∈ s then E k j else E k i)
      (fun k => if k ∈ insert k₀ s then E k j else E k i) hsim
    -- at `k₀` the step is exactly from column `i` to column `j`
    rw [if_neg hk₀, if_pos (Finset.mem_insert_self k₀ s)] at hstep
    have htri := abs_sub_le (PolyZonotope.monomial E a i)
      (∏ k, a k ^ (if k ∈ s then E k j else E k i))
      (∏ k, a k ^ (if k ∈ insert k₀ s then E k j else E k i))
    rw [Finset.sum_insert hk₀]
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two monomials drift by at most the sum over every factor of the `eDiff` of
their exponents there, whatever the two exponent columns are. -/
theorem PolyZonotope.abs_sub_monomial_le_sum {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) (i j : Fin h) :
    |PolyZonotope.monomial E a i - PolyZonotope.monomial E a j|
      ≤ ∑ k, (PolyZonotope.eDiff (E k i) (E k j) : ℝ) := by -- --- PROOF ---
  have h1 : ∀ k, (if k ∈ (Finset.univ : Finset (Fin p)) then E k j else E k i) = E k j :=
    fun k => if_pos (Finset.mem_univ k)
  -- the last hybrid, every exponent moved, is the monomial at `j`
  have hfull := PolyZonotope.aux_abs_sub_hybrid_le E ha i j Finset.univ
  simp only [h1] at hfull
  rwa [show (∏ k, a k ^ E k j) = PolyZonotope.monomial E a j from rfl] at hfull

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

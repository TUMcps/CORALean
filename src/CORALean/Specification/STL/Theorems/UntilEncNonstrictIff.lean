module

public import CORALean.Specification.STL.Definitions.MILPEncoding

@[expose] public section

/-!
# The unbounded until of the encoding, unrolled

The recursion `z_i = (z^{φ₂}_i ∧ z^{φ₁}_i) ∨ (z^{φ₁}_i ∧ z_{i+1})`, `z_N = z^{φ₂}_N ∧ z^{φ₁}_N`, the
non-strict reading of [1, Sec. IV-B.3 (until)], holds at `i ≤ N` iff `φ₂` holds at some
`t₁ ∈ [i, N]` and `φ₁` on all of `[i, t₁]`: the unbounded until over the horizon, with the
printed semantics' closed interval.

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.untilEnc_nonstrict_iff {N : ℕ} {P Q : ℕ → Prop} :
    ∀ i, i ≤ N → (STL.untilEnc N true P Q i ↔
      ∃ t₁ ∈ Finset.Icc i N, Q t₁ ∧ ∀ s ∈ Finset.Icc i t₁, P s) := by -- --- PROOF ---
  intro i
  induction hk : N - i using Nat.strong_induction_on generalizing i with
  | _ k ih =>
  intro hi
  rw [STL.untilEnc]
  simp only [if_true]
  by_cases hiN : i < N
  · -- one step: `t₁ = i`, or `φ₁` at `i` and a later `t₁`
    rw [if_pos hiN, ih (N - (i + 1)) (by omega) (i + 1) rfl (by omega)]
    constructor
    · rintro (⟨hQ, hP⟩ | ⟨hP, t₁, ht₁, hQ, hPs⟩)
      · exact ⟨i, Finset.mem_Icc.mpr ⟨le_rfl, hi⟩, hQ, fun s hs => by
          rw [Finset.mem_Icc] at hs; rwa [show s = i by omega]⟩
      · refine ⟨t₁, Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp ht₁).1; omega,
          (Finset.mem_Icc.mp ht₁).2⟩, hQ, fun s hs => ?_⟩
        rw [Finset.mem_Icc] at hs
        by_cases hsi : s = i
        · rwa [hsi]
        · exact hPs s (Finset.mem_Icc.mpr ⟨by omega, hs.2⟩)
    · rintro ⟨t₁, ht₁, hQ, hPs⟩
      rw [Finset.mem_Icc] at ht₁
      have hPi := hPs i (Finset.mem_Icc.mpr ⟨le_rfl, ht₁.1⟩)
      by_cases ht : t₁ = i
      · subst ht; exact Or.inl ⟨hQ, hPi⟩
      · exact Or.inr ⟨hPi, t₁, Finset.mem_Icc.mpr ⟨by omega, ht₁.2⟩, hQ,
          fun s hs => hPs s (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hs).1; omega,
            (Finset.mem_Icc.mp hs).2⟩)⟩
  · -- at the horizon: only `t₁ = N`
    have hiN' : i = N := by omega
    subst hiN'
    rw [if_neg hiN]
    constructor
    · rintro ⟨hQ, hP⟩
      exact ⟨i, Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩, hQ, fun s hs => by
        rw [Finset.mem_Icc] at hs; rwa [show s = i by omega]⟩
    · rintro ⟨t₁, ht₁, hQ, hPs⟩
      rw [Finset.mem_Icc] at ht₁
      have : t₁ = i := by omega
      subst this
      exact ⟨hQ, hPs t₁ (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

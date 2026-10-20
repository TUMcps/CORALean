module

public import CORALean.Specification.STL.Theorems.UntilEncNonstrictIff

@[expose] public section

/-!
# The bounded until from the unbounded one

[1, Sec. IV-B.3 (until)], after Donzé, Ferrère and Maler:
`φ₁ U[a,b] φ₂ = □[0,a] φ₁ ∧ ◇[a,b] φ₂ ∧ ◇[a,a](φ₁ U φ₂)`, here over the horizon `N ≥ t + b`
with the non-strict unbounded until: `φ₁` on `[t, t+a]`, `φ₂` somewhere in `[t+a, t+b]`, and
the unbounded until at `t + a` hold together iff `φ₂` holds at some `t' ∈ [t+a, t+b]` and `φ₁`
on all of `[t, t']`. Of the two witnesses the earlier serves.

## Inputs
* `N` – horizon
* `t` – time step
* `a` – interval lower bound
* `b` – interval upper bound
* `P` – left operand values
* `Q` – right operand values

## Hypotheses
* `hab` – the bounds are ordered
* `hN` – the interval fits in the horizon

## Conclusion
* the bounded until decomposes into the unbounded one

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

theorem STL.until_decomp_iff {N t a b : ℕ} (hab : a ≤ b) (hN : t + b ≤ N) {P Q : ℕ → Prop} :
    ((∀ s ∈ Finset.Icc t (t + a), P s) ∧ (∃ s ∈ Finset.Icc (t + a) (t + b), Q s) ∧
      STL.untilEnc N true P Q (t + a)) ↔
      ∃ t' ∈ Finset.Icc (t + a) (t + b), Q t' ∧ ∀ s ∈ Finset.Icc t t', P s := by -- --- PROOF ---
  rw [STL.untilEnc_nonstrict_iff (t + a) (by omega)]
  constructor
  · rintro ⟨hA, ⟨t₂, ht₂, hQ₂⟩, ⟨t₁, ht₁, hQ₁, hP₁⟩⟩
    rw [Finset.mem_Icc] at ht₁ ht₂
    -- the earlier of the two witnesses
    by_cases h : t₁ ≤ t₂
    · refine ⟨t₁, Finset.mem_Icc.mpr ⟨ht₁.1, by omega⟩, hQ₁, fun s hs => ?_⟩
      rw [Finset.mem_Icc] at hs
      by_cases hsa : s ≤ t + a
      · exact hA s (Finset.mem_Icc.mpr ⟨hs.1, hsa⟩)
      · exact hP₁ s (Finset.mem_Icc.mpr ⟨by omega, hs.2⟩)
    · refine ⟨t₂, Finset.mem_Icc.mpr ht₂, hQ₂, fun s hs => ?_⟩
      rw [Finset.mem_Icc] at hs
      by_cases hsa : s ≤ t + a
      · exact hA s (Finset.mem_Icc.mpr ⟨hs.1, hsa⟩)
      · exact hP₁ s (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · rintro ⟨t', ht', hQ, hP⟩
    rw [Finset.mem_Icc] at ht'
    refine ⟨fun s hs => hP s ?_, ⟨t', Finset.mem_Icc.mpr ht', hQ⟩,
      ⟨t', Finset.mem_Icc.mpr ⟨ht'.1, by omega⟩, hQ, fun s hs => hP s ?_⟩⟩
    · rw [Finset.mem_Icc] at hs ⊢; omega
    · rw [Finset.mem_Icc] at hs ⊢; omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

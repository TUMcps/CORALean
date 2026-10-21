module

public import CORALean.ContSet.Interval.Real.Theorems.PowerBetween
public import CORALean.ContSet.Interval.Real.Operations.IsNonempty
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Topology.Algebra.Monoid

@[expose] public section

/-!
# `Interval.power` is exactly the image under `x ↦ x ^ k`

For a nonempty box. Each bound is attained at a point of `{a, 0, b}` inside
`[a, b]` (the lower bound `0` of an even power at `x = 0`), and the power is
continuous, so the intermediate value theorem fills everything between.

[1, Eq. 9], all three cases, for `k ≥ 1`; at `k = 0` the range is `{1}`.

## Inputs
* `I` – interval box
* `k` – exponent

## Hypotheses
* `hI` – `I` nonempty

## Conclusion
* the power box is exactly the image of `I` under the power

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Both bounds are attained inside `[a, b]`. -/
theorem Interval.aux_pow_attained {a b : ℝ} (hab : a ≤ b) (k : ℕ) : -- --- CONCL ---
    (∃ p, a ≤ p ∧ p ≤ b ∧ p ^ k =
      if k % 2 = 0 ∧ k ≠ 0 ∧ a < 0 ∧ 0 < b then 0 else min (a ^ k) (b ^ k)) ∧
    (∃ q, a ≤ q ∧ q ≤ b ∧ q ^ k = max (a ^ k) (b ^ k)) := by -- --- PROOF ---
  refine ⟨?_, ?_⟩
  · by_cases hs : k % 2 = 0 ∧ k ≠ 0 ∧ a < 0 ∧ 0 < b
    · exact ⟨0, hs.2.2.1.le, hs.2.2.2.le, by rw [if_pos hs, zero_pow hs.2.1]⟩
    · rw [if_neg hs]
      rcases min_choice (a ^ k) (b ^ k) with h | h
      · exact ⟨a, le_rfl, hab, h.symm⟩
      · exact ⟨b, hab, le_rfl, h.symm⟩
  · rcases max_choice (a ^ k) (b ^ k) with h | h
    · exact ⟨a, le_rfl, hab, h.symm⟩
    · exact ⟨b, hab, le_rfl, h.symm⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.power_exact (I : Interval (Vec ℝ n)) (hI : I.IsNonempty) (k : ℕ) : -- --- CONCL ---
    (I.power k).construct = (fun x i => x i ^ k) '' I.construct := by -- --- PROOF ---
  ext z
  constructor
  · intro hz
    -- per coordinate: both bounds are attained, then the intermediate value theorem
    have h : ∀ i, ∃ y, (I.inf i ≤ y ∧ y ≤ I.sup i) ∧ y ^ k = z i := by
      intro i
      obtain ⟨⟨p, hp1, hp2, hp⟩, ⟨q, hq1, hq2, hq⟩⟩ := Interval.aux_pow_attained (hI i) k
      have hz' : (if k % 2 = 0 ∧ k ≠ 0 ∧ I.inf i < 0 ∧ 0 < I.sup i then 0
          else min (I.inf i ^ k) (I.sup i ^ k)) ≤ z i ∧
          z i ≤ max (I.inf i ^ k) (I.sup i ^ k) := hz i
      have hp' : p ^ k = if k % 2 = 0 ∧ k ≠ 0 ∧ I.inf i < 0 ∧ 0 < I.sup i then 0
          else min (I.inf i ^ k) (I.sup i ^ k) := hp
      have hq' : q ^ k = max (I.inf i ^ k) (I.sup i ^ k) := hq
      rw [← hp', ← hq'] at hz'
      have hmem : z i ∈ Set.uIcc (p ^ k) (q ^ k) := Set.Icc_subset_uIcc hz'
      obtain ⟨y, hy, hyz⟩ := intermediate_value_uIcc
        (f := fun x : ℝ => x ^ k) (continuous_pow k).continuousOn hmem
      have hy' := Set.uIcc_subset_Icc ⟨hp1, hp2⟩ ⟨hq1, hq2⟩ hy
      exact ⟨y, hy', hyz⟩
    choose y hy hyz using h
    exact ⟨y, fun i => hy i, funext hyz⟩
  · rintro ⟨x, hx, rfl⟩ i
    exact Interval.pow_between k (hx i).1 (hx i).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

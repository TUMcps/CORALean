import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Measure.Real

/-!
# At most `k` of `m` independent samples in a set

The binomial step of [1, Thm. 3]'s proof (Appendix B, Eq. B.3): under the product `Pᵐ` of a
probability `P`, the samples `b_j` of which at most `k` fall in a measurable `V` have probability
at most `Σ_{i=0}^k C(m, i) ζⁱ(1 - ζ)^{m-i}`, with `ζ = P(V)`. The samples falling in `V` are
exactly one set `I` of indices, so the event is covered by the boxes `∏_j (V if j ∈ I, else Vᶜ)`,
`|I| ≤ k`, each of measure `ζ^{|I|}(1 - ζ)^{m-|I|}`; there are `C(m, i)` of each size `i`. The
boxes are disjoint, so this is the exact probability, but only the bound is needed.
## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory

variable {ι Δ : Type} [MeasurableSpace Δ]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the subsets of at most `k` indices, summed by size
theorem aux_sum_powerset_card_le [DecidableEq ι] (m k : ℕ) (g : ℕ → ℝ) (s : Finset ι)
    (hs : s.card = m) :
    ∑ I ∈ s.powerset with I.card ≤ k, g I.card =
      ∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ) * g i := by -- --- PROOF ---
  rw [Finset.sum_filter, Finset.sum_powerset_apply_card (fun i => if i ≤ k then g i else 0), hs]
  simp only [nsmul_eq_mul]
  -- both sides are the sum up to `m + k`, the terms above `m` or `k` vanishing
  have h1 : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (if i ≤ k then g i else 0) =
      ∑ i ∈ Finset.range (m + k + 1), (m.choose i : ℝ) * (if i ≤ k then g i else 0) := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i _ hi => ?_
    simp only [Finset.mem_range, not_lt] at hi
    simp [Nat.choose_eq_zero_of_lt (show m < i by omega)]
  have h2 : ∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ) * g i =
      ∑ i ∈ Finset.range (m + k + 1), (m.choose i : ℝ) * (if i ≤ k then g i else 0) := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show k + 1 ≤ m + k + 1 by omega))
      fun i _ hi => by simp only [Finset.mem_range, not_lt] at hi; simp [show ¬ i ≤ k by omega]]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [show i ≤ k by simpa [Nat.lt_succ_iff] using hi]
  rw [h1, h2]


-- =======================================  MAIN THEOREM  ======================================= --

open scoped Classical in
theorem measure_pi_card_filter_le [Fintype ι] (P : Measure Δ) [IsProbabilityMeasure P] {V : Set Δ}
    (hV : MeasurableSet V) (k : ℕ) :
    Measure.pi (fun _ : ι => P) {b | (Finset.univ.filter fun j => b j ∈ V).card ≤ k} ≤
      ENNReal.ofReal (∑ i ∈ Finset.range (k + 1), ((Fintype.card ι).choose i : ℝ) *
        P.real V ^ i * (1 - P.real V) ^ (Fintype.card ι - i)) := by -- --- PROOF ---
  set m := Fintype.card ι
  set p := P.real V
  let box : Finset ι → Set (ι → Δ) := fun I => Set.pi Set.univ fun j => if j ∈ I then V else Vᶜ
  -- every outcome lies in the box of the indices that fall in `V`
  have hcover : {b : ι → Δ | (Finset.univ.filter fun j => b j ∈ V).card ≤ k} ⊆
      ⋃ I ∈ Finset.univ.powerset.filter (fun I : Finset ι => I.card ≤ k), box I := by
    intro b hb
    refine Set.mem_biUnion (x := Finset.univ.filter fun j => b j ∈ V) (by simpa using hb) ?_
    intro j _
    by_cases h : b j ∈ V <;> simp [h]
  have hP : P V = ENNReal.ofReal p := (ofReal_measureReal (measure_ne_top P V)).symm
  have hPc : P Vᶜ = ENNReal.ofReal (1 - p) := by
    rw [prob_compl_eq_one_sub hV, hP, ← ENNReal.ofReal_one, ENNReal.ofReal_sub _ measureReal_nonneg]
  -- each box has the measure of its pattern
  have hbox : ∀ I : Finset ι, Measure.pi (fun _ : ι => P) (box I) =
      ENNReal.ofReal (p ^ I.card * (1 - p) ^ (m - I.card)) := by
    intro I
    rw [Measure.pi_pi]
    have : ∀ j, P (if j ∈ I then V else Vᶜ) = if j ∈ I then P V else P Vᶜ := fun j => by
      split_ifs <;> rfl
    simp only [this]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
      Finset.univ_inter, Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, hP, hPc,
      ENNReal.ofReal_mul (pow_nonneg measureReal_nonneg _), ENNReal.ofReal_pow measureReal_nonneg,
      ENNReal.ofReal_pow (by simp [p, measureReal_le_one])]
  calc Measure.pi (fun _ : ι => P) {b | (Finset.univ.filter fun j => b j ∈ V).card ≤ k}
      ≤ ∑ I ∈ Finset.univ.powerset.filter (fun I : Finset ι => I.card ≤ k),
          Measure.pi (fun _ : ι => P) (box I) :=
        (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
    -- in real numbers, then grouped by the size of `I`
    _ = ENNReal.ofReal (∑ I ∈ Finset.univ.powerset.filter (fun I : Finset ι => I.card ≤ k),
          p ^ I.card * (1 - p) ^ (m - I.card)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun I _ =>
          mul_nonneg (pow_nonneg measureReal_nonneg _)
            (pow_nonneg (by simp [p, measureReal_le_one]) _)]
        exact Finset.sum_congr rfl fun I _ => hbox I
    _ = _ := by
        rw [aux_sum_powerset_card_le m k (fun i => p ^ i * (1 - p) ^ (m - i)) Finset.univ
          Finset.card_univ]
        simp only [mul_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

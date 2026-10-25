module

public import CORALean.ContSet.Zonotope.Real.Operations.SplitPivot
public import CORALean.ContSet.Zonotope.Real.Theorems.CrossNonnegOfArgLe
public import CORALean.ContSet.Zonotope.Real.Theorems.CrossPosOfArgLt
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# The pivot split of [1, Alg. 4] divides the generators in angle order

For generators of one horizontal direction `σ` (`σ·x > 0`) in the upper half-plane and the pivot
`s = ∑ 2g`, `splitPivot` returns two nonempty parts that make up `G`, every generator of the first
at no later angle than every one of the second, `σ·cross(g_i, g_j) ≥ 0`. The cross products of the
generators with the pivot sum to `cross(s/2, s) = 0`, so they are not all of one sign, which is
why neither part is empty; and if the first part would be empty they all vanish, the generators are
parallel, and the fallback split off the least index is order-free.

## Inputs
* `Z` – planar zonotope
* `right` – direction flag
* `σ` – search direction
* `G` – generator set
* `s` – sum of the doubled generators

## Hypotheses
* `hH` – generators point upward
* `hσ` – direction matches the flag
* `hG` – generators point along `σ`
* `hcard` – more than one generator
* `hs` – `s` is the doubled sum

## Conclusion
* the pivot splits the generators into two ordered nonempty parts

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems Reachability
      Analysis". Hybrid Systems: Computation and Control, 2008.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The three order facts at the pivot, uniformly in the direction `σ`. -/
theorem Zonotope.aux_pivot_order {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {u w v : Vec ℝ 2}
    (hu : 0 ≤ u 1 ∧ (0 < u 1 ∨ 0 ≤ u 0)) (hw : 0 ≤ w 1 ∧ (0 < w 1 ∨ 0 ≤ w 0))
    (hv : 0 ≤ v 1 ∧ (0 < v 1 ∨ 0 ≤ v 0)) (hu0 : u ≠ 0) (hv0 : v ≠ 0) : -- --- CONCL ---
    (σ * Complex.arg ⟨u 0, u 1⟩ < σ * Complex.arg ⟨v 0, v 1⟩ →
      0 < σ * (u 0 * v 1 - u 1 * v 0)) ∧
    (¬ σ * Complex.arg ⟨w 0, w 1⟩ < σ * Complex.arg ⟨v 0, v 1⟩ →
      0 ≤ σ * (v 0 * w 1 - v 1 * w 0)) ∧
    (σ * Complex.arg ⟨u 0, u 1⟩ < σ * Complex.arg ⟨v 0, v 1⟩ →
      ¬ σ * Complex.arg ⟨w 0, w 1⟩ < σ * Complex.arg ⟨v 0, v 1⟩ →
      0 ≤ σ * (u 0 * w 1 - u 1 * w 0)) := by -- --- PROOF ---
  rcases hσ with rfl | rfl
  · refine ⟨fun h => ?_, fun h => ?_, fun h h' => ?_⟩
    · simpa using Zonotope.cross_pos_of_arg_lt hu.1 hv hu0 hv0 (by simpa using h)
    · simpa using Zonotope.cross_nonneg_of_arg_le hv.1 (by simpa using h)
    · simpa using Zonotope.cross_nonneg_of_arg_le hu.1
        (le_trans (by simpa using h.le) (by simpa using h'))
  · refine ⟨fun h => ?_, fun h => ?_, fun h h' => ?_⟩
    · have := Zonotope.cross_pos_of_arg_lt hv.1 hu hv0 hu0 (by simpa using h)
      linarith
    · have := Zonotope.cross_nonneg_of_arg_le hw.1 (by simpa using h)
      linarith
    · have := Zonotope.cross_nonneg_of_arg_le hw.1
        (le_trans (by simpa using h') (by simpa using h.le))
      linarith

/-- The pivot is in the upper half-plane and points along `σ`. -/
theorem Zonotope.aux_pivot_half_plane (Z : Zonotope (Vec ℝ 2)) {σ : ℝ}
    (hH : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0)) (G : Finset (Fin Z.h))
    (hG : ∀ i ∈ G, 0 < σ * Z.G i 0) (hne : G.Nonempty) {s : Vec ℝ 2}
    (hs : s = ∑ i ∈ G, (2 : ℝ) • Z.G i) : -- --- CONCL ---
    0 < σ * s 0 ∧ (0 ≤ s 1 ∧ (0 < s 1 ∨ 0 ≤ s 0)) := by -- --- PROOF ---
  have hs0 : s 0 = ∑ i ∈ G, 2 * Z.G i 0 := by
    rw [hs]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hs1 : s 1 = ∑ i ∈ G, 2 * Z.G i 1 := by
    rw [hs]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hpos : 0 < σ * s 0 := by
    rw [hs0, Finset.mul_sum]
    exact Finset.sum_pos (fun i hi => by linarith [hG i hi]) hne
  have h1 : 0 ≤ s 1 := by
    rw [hs1]; exact Finset.sum_nonneg fun i _ => by linarith [(hH i).1]
  refine ⟨hpos, h1, ?_⟩
  rcases h1.eq_or_lt with h | h
  · -- all the heights vanish, so the generators point right
    right
    rw [hs0]
    refine Finset.sum_nonneg fun i hi => ?_
    have hz : Z.G i 1 = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => by show 0 ≤ 2 * Z.G i 1; linarith [(hH i).1])).mp
        (by rw [← hs1]; exact h.symm) i hi
      linarith
    rcases (hH i).2 with h' | h'
    · linarith
    · linarith
  · exact Or.inl h


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.splitPivot_spec (Z : Zonotope (Vec ℝ 2))
    (hH : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0)) (right : Bool) {σ : ℝ}
    (hσ : σ = if right then 1 else -1) (G : Finset (Fin Z.h))
    (hG : ∀ i ∈ G, 0 < σ * Z.G i 0) (hcard : 1 < G.card) {s : Vec ℝ 2}
    (hs : s = ∑ i ∈ G, (2 : ℝ) • Z.G i) : -- --- CONCL ---
    (Z.splitPivot right G s).1.Nonempty ∧ (Z.splitPivot right G s).2.Nonempty ∧
    (Z.splitPivot right G s).1 ∪ (Z.splitPivot right G s).2 = G ∧
    Disjoint (Z.splitPivot right G s).1 (Z.splitPivot right G s).2 ∧
    ∀ i ∈ (Z.splitPivot right G s).1, ∀ j ∈ (Z.splitPivot right G s).2,
      0 ≤ σ * (Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0) := by -- --- PROOF ---
  classical
  have hσ' : σ = 1 ∨ σ = -1 := by cases right <;> simp [hσ]
  have hne : G.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hs0, hsH⟩ := Zonotope.aux_pivot_half_plane Z hH G hG hne hs
  have hsne : s ≠ 0 := fun h => by simp [h] at hs0
  have hgne : ∀ i ∈ G, Z.G i ≠ 0 := fun i hi h => by
    have := hG i hi; simp [h] at this
  -- the cross products with the pivot sum to zero
  have hsum : ∑ i ∈ G, (Z.G i 0 * s 1 - Z.G i 1 * s 0) = 0 := by
    have e0 : s 0 = 2 * ∑ i ∈ G, Z.G i 0 := by
      rw [hs]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    have e1 : s 1 = 2 * ∑ i ∈ G, Z.G i 1 := by
      rw [hs]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    rw [e0, e1]; ring
  -- the parts, ordered against the pivot
  have hlt : ∀ a b : ℝ, (if right then a < b else b < a) ↔ σ * a < σ * b := fun a b => by
    cases right <;> simp [hσ]
  have horder := fun i (hi : i ∈ G) j (hj : j ∈ G) => Zonotope.aux_pivot_order hσ' (hH i) (hH j)
    hsH (hgne i hi) hsne
  unfold Zonotope.splitPivot
  simp only [hlt]
  by_cases hG1 : (G.filter fun x => σ * Complex.arg ⟨Z.G x 0, Z.G x 1⟩
      < σ * Complex.arg ⟨s 0, s 1⟩).Nonempty
  · rw [if_pos hG1]
    simp only
    refine ⟨hG1, ?_, Finset.union_sdiff_of_subset (Finset.filter_subset _ _),
      Finset.disjoint_sdiff, fun i hi j hj => ?_⟩
    · -- not all of `G` is below the pivot, or the cross products with it would sum positive
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hempty
      have hpos : 0 < ∑ i ∈ G, σ * (Z.G i 0 * s 1 - Z.G i 1 * s 0) :=
        Finset.sum_pos (fun i hi => (horder i hi i hi).1
          (Finset.mem_filter.mp (hempty hi)).2) hne
      rw [← Finset.mul_sum, hsum] at hpos
      simp at hpos
    · obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
      obtain ⟨hj1, hj2⟩ := Finset.mem_sdiff.mp hj
      exact (horder i hi1 j hj1).2.2 hi2 (fun h => hj2 (Finset.mem_filter.mpr ⟨hj1, h⟩))
  · rw [if_neg hG1]
    simp only [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hG1
    -- everything is at or beyond the pivot, so all cross products with it vanish
    have hzero : ∀ i ∈ G, Z.G i 0 * s 1 - Z.G i 1 * s 0 = 0 := by
      have hnn : ∀ i ∈ G, 0 ≤ σ * (s 0 * Z.G i 1 - s 1 * Z.G i 0) := fun i hi =>
        (horder i hi i hi).2.1 (hG1 hi)
      have hs' : ∑ i ∈ G, σ * (s 0 * Z.G i 1 - s 1 * Z.G i 0) = 0 := by
        have : ∑ i ∈ G, σ * (s 0 * Z.G i 1 - s 1 * Z.G i 0)
            = -(σ * ∑ i ∈ G, (Z.G i 0 * s 1 - Z.G i 1 * s 0)) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [this, hsum]; ring
      intro i hi
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hs' i hi
      have hσne : σ ≠ 0 := by rcases hσ' with h | h <;> rw [h] <;> norm_num
      have := (mul_eq_zero.mp this).resolve_left hσne
      linarith
    -- so all generators are parallel
    have hpar : ∀ i ∈ G, ∀ j ∈ G, Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0 = 0 := by
      intro i hi j hj
      have h0 : (Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0) * s 0 = 0 := by
        linear_combination (-Z.G i 0) * hzero j hj + Z.G j 0 * hzero i hi
      have hs0' : s 0 ≠ 0 := fun h => by simp [h] at hs0
      exact (mul_eq_zero.mp h0).resolve_right hs0'
    simp only
    have hmin : (G.filter fun i => ∀ j ∈ G, i ≤ j).Nonempty :=
      ⟨G.min' hne, Finset.mem_filter.mpr ⟨Finset.min'_mem G hne, fun j hj => Finset.min'_le G j hj⟩⟩
    refine ⟨hmin, ?_, Finset.filter_union_filter_not_eq _ _,
      Finset.disjoint_filter_filter_not _ _ _, fun i hi j hj => ?_⟩
    · by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hempty
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
      exact hab (le_antisymm (not_not.mp (hempty ha) b hb) (not_not.mp (hempty hb) a ha))
    · rw [hpar i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1]
      simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

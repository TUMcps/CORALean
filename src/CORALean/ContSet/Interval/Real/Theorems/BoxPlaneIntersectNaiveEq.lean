module

public import CORALean.ContSet.Interval.Real.Operations.BoxPlaneIntersectNaive
public import CORALean.ContSet.Interval.Real.Theorems.EdgeMemHyperplaneIff
public import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsInterHyperplaneIff
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# The naive algorithm returns exactly the vertices of the cut

[1, Alg. 1] traverses all edges and collects `e_uv(t⋆)` for `t⋆ ∈ [0, 1]`; the problem is to
compute the vertices of the polygon `B ∩ P`. Its output is exactly the set of extreme points
of `B ∩ {Σᵢ xᵢ = α}`: an edge meets the plane at most once, at `t⋆`, [1, Eq. 4], and the extreme
points are the points of the cut on an edge, [1, Sec. 1]. For a box with positive side lengths,
where `t⋆` divides by an edge length, and `n ≥ 1`: a `0`-dimensional box has no edge at all.

## Inputs
* `I` – interval box
* `α` – level of the plane

## Hypotheses
* `hn` – dimension positive
* `hI` – lower bounds strictly below upper bounds

## Conclusion
* the naive algorithm returns exactly the vertices of the cut

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of the edge from `corner l` raising `j`, coordinate by coordinate. -/
theorem aux_edge_apply {I : Interval (Vec ℝ n)} {l : Fin n → Bool} {j : Fin n} (hlj : l j = false)
    (t : ℝ) (k : Fin n) :
    (I.corner l + t • (I.corner (Function.update l j true) - I.corner l)) k =
      if k = j then I.inf j + t * (I.sup j - I.inf j) else I.corner l k := by
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Interval.corner]
  by_cases hk : k = j
  · subst hk; simp [hlj]
  · simp [hk]

/-- The edge's length is the denominator of `t⋆`. -/
theorem aux_edge_den {I : Interval (Vec ℝ n)} {l : Fin n → Bool} {j : Fin n}
    (hlj : l j = false) : -- --- CONCL ---
    ∑ i, (I.corner (Function.update l j true) i - I.corner l i) =
      I.sup j - I.inf j := by -- --- PROOF ---
  have : ∀ i, I.corner (Function.update l j true) i - I.corner l i =
      if i = j then I.sup j - I.inf j else 0 := fun i => by
    simp only [Interval.corner]
    by_cases hi : i = j
    · subst hi; simp [hlj]
    · simp [hi]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.boxPlaneIntersectNaive_eq {I : Interval (Vec ℝ n)} (hn : 0 < n)
    (hI : ∀ i, I.inf i < I.sup i) (α : ℝ) : -- --- CONCL ---
    ↑(I.boxPlaneIntersectNaive α) =
      Set.extremePoints ℝ (I.construct ∩ Interval.hyperplane 1 α) := by -- --- PROOF ---
  classical
  -- membership in the output: a point of some edge, at a `t ∈ [0, 1]`, on the plane
  have hmem : ∀ x, x ∈ I.boxPlaneIntersectNaive α ↔ ∃ l : Fin n → Bool, ∃ j, l j = false ∧
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        x = I.corner l + t • (I.corner (Function.update l j true) - I.corner l) ∧
        x ∈ Interval.hyperplane 1 α := fun x => by
    unfold Interval.boxPlaneIntersectNaive
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
    constructor
    -- an output point: its edge's `t⋆` is in `[0, 1]`, and the point is on the plane
    · rintro ⟨l, j, hlj, hx⟩
      have hden := aux_edge_den (I := I) hlj
      have hd : ∑ i, (I.corner (Function.update l j true) i - I.corner l i) ≠ 0 := by
        rw [hden]; linarith [hI j]
      split_ifs at hx with ht
      · rw [Finset.mem_singleton] at hx
        refine ⟨l, j, hlj, _, ht.1, ht.2, hx, ?_⟩
        rw [hx, Interval.edge_mem_hyperplane_iff hd]
      · simp at hx
    -- conversely the plane fixes `t` to `t⋆`, which is then in `[0, 1]`
    · rintro ⟨l, j, hlj, t, ht0, ht1, rfl, hP⟩
      have hden := aux_edge_den (I := I) hlj
      have hd : ∑ i, (I.corner (Function.update l j true) i - I.corner l i) ≠ 0 := by
        rw [hden]; linarith [hI j]
      have ht := (Interval.edge_mem_hyperplane_iff hd).mp hP
      refine ⟨l, j, hlj, ?_⟩
      rw [← ht, if_pos ⟨ht0, ht1⟩, Finset.mem_singleton]
  ext x
  rw [Finset.mem_coe, hmem, Interval.mem_extremePoints_inter_hyperplane_iff (a := 1)
    (fun _ => by simp)]
  constructor
  · -- a point of an edge is in the box, and every coordinate but `j` is at a bound
    rintro ⟨l, j, hlj, t, ht0, ht1, rfl, hP⟩
    refine ⟨⟨fun k => ?_, hP⟩, fun k k' hkk' => ?_⟩
    · change I.inf k ≤ (I.corner l + t • (I.corner (Function.update l j true) - I.corner l)) k ∧
        (I.corner l + t • (I.corner (Function.update l j true) - I.corner l)) k ≤ I.sup k
      rw [aux_edge_apply hlj]
      have hk := (hI k).le
      split_ifs with hkj
      · subst hkj; constructor <;> nlinarith
      · simp only [Interval.corner]; split_ifs <;> constructor <;> linarith
    · by_cases hkj : k = j
      · right
        have : k' ≠ j := fun h => hkk' (hkj.trans h.symm)
        rw [aux_edge_apply hlj, if_neg this]
        simp only [Interval.corner]; split_ifs <;> simp
      · left
        rw [aux_edge_apply hlj, if_neg hkj]
        simp only [Interval.corner]; split_ifs <;> simp
  · rintro ⟨⟨hxB, hxP⟩, hedge⟩
    have hxB' : ∀ k, I.inf k ≤ x k ∧ x k ≤ I.sup k := hxB
    by_cases hint : ∃ m, x m ≠ I.inf m ∧ x m ≠ I.sup m
    · -- one coordinate inside: the edge raising it from the corner below `x`
      obtain ⟨m, hm1, hm2⟩ := hint
      have hbd : ∀ k, k ≠ m → x k = I.inf k ∨ x k = I.sup k := fun k hk =>
        (hedge k m hk).resolve_right (by simp [hm1, hm2])
      let l : Fin n → Bool := fun k => if k = m then false else decide (x k = I.sup k)
      have hd : 0 < I.sup m - I.inf m := by linarith [hI m]
      refine ⟨l, m, by simp [l], (x m - I.inf m) / (I.sup m - I.inf m),
        div_nonneg (by linarith [(hxB' m).1]) hd.le,
        (div_le_one hd).mpr (by linarith [(hxB' m).2]), funext fun k => ?_, hxP⟩
      rw [aux_edge_apply (by simp [l])]
      split_ifs with hkm
      · subst hkm; field_simp; ring
      · simp only [Interval.corner, l, hkm, if_false]
        by_cases hxs : x k = I.sup k
        · simp [hxs]
        · simp only [hxs, decide_false]
          exact ((hbd k hkm).resolve_right hxs)
    · -- `x` is a vertex: an edge starting or ending there, at `t = 0` or `t = 1`
      simp only [not_exists, not_and, not_not] at hint
      let l : Fin n → Bool := fun k => decide (x k = I.sup k)
      have hlx : I.corner l = x := funext fun k => by
        simp only [Interval.corner, l]
        by_cases hxs : x k = I.sup k
        · simp [hxs]
        · simp only [hxs, decide_false]
          by_contra h; exact hxs (hint k (Ne.symm h))
      let j0 : Fin n := ⟨0, hn⟩
      by_cases hl0 : l j0 = false
      · refine ⟨l, j0, hl0, 0, le_rfl, zero_le_one, ?_, hxP⟩
        rw [zero_smul, add_zero, hlx]
      · rw [Bool.not_eq_false] at hl0
        refine ⟨Function.update l j0 false, j0, by simp, 1, zero_le_one, le_rfl, ?_, hxP⟩
        rw [one_smul, add_sub_cancel, Function.update_idem,
          Function.update_eq_self_iff.mpr hl0.symm, hlx]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

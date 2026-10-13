module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Normed.Field.Lemmas

@[expose] public section

/-!
# The reciprocal of an interval, case by case

[1, Eq. 3] gives `1/[y]` in five cases, read here on the set `{1/y | y ∈ [y], y ≠ 0}`: empty at
`[0, 0]`, `[1/y̅, 1/y̲]` when `0 ∉ [y]`, the half-lines `[1/y̅, ∞[` and `]-∞, 1/y̲]` when `0` is an
end, and `]-∞, ∞[` when `0` is inside. The first four are the set exactly; in the last the set is
`]-∞, 1/y̲] ∪ [1/y̅, ∞[`, unbounded both ways, so `]-∞, ∞[` is its interval hull, the interval
answer [1] intends. The quotient `[x]/[y] = [x]·(1/[y])` is `x / y = x · y⁻¹`; on boxes away from
`0` it is `Interval.rdivide_exact`.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- On positive values the reciprocal takes every value from `1/hi` up. -/
theorem aux_inv_image_Ioc (hi : ℝ) (hhi : 0 < hi) :
    (·⁻¹) '' (Set.Icc 0 hi ∩ {y | y ≠ 0}) = Set.Ici hi⁻¹ := by -- --- PROOF ---
  ext v
  constructor
  · rintro ⟨y, ⟨hy, hy0⟩, rfl⟩
    have hy' : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
    exact (inv_le_inv₀ hhi hy').2 hy.2
  · intro hv
    have hv0 : 0 < v := lt_of_lt_of_le (inv_pos.2 hhi) hv
    refine ⟨v⁻¹, ⟨⟨(inv_pos.2 hv0).le, ?_⟩, inv_ne_zero hv0.ne'⟩, inv_inv v⟩
    exact (inv_le_comm₀ hhi hv0).1 hv


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 3], the five cases of `1/[y]`. -/
theorem Interval.inv_image_Icc_cases {lo hi : ℝ} (hle : lo ≤ hi) :
    (lo = 0 ∧ hi = 0 → (·⁻¹) '' (Set.Icc lo hi ∩ {y | y ≠ 0}) = ∅) ∧
    (0 < lo ∨ hi < 0 →
      (·⁻¹) '' (Set.Icc lo hi ∩ {y | y ≠ 0}) = Set.Icc hi⁻¹ lo⁻¹) ∧
    (lo = 0 ∧ 0 < hi → (·⁻¹) '' (Set.Icc lo hi ∩ {y | y ≠ 0}) = Set.Ici hi⁻¹) ∧
    (lo < 0 ∧ hi = 0 → (·⁻¹) '' (Set.Icc lo hi ∩ {y | y ≠ 0}) = Set.Iic lo⁻¹) ∧
    (lo < 0 ∧ 0 < hi → ¬BddAbove ((·⁻¹) '' (Set.Icc lo hi ∩ {y | y ≠ 0})) ∧
      ¬BddBelow ((·⁻¹) '' (Set.Icc lo hi ∩ {y | y ≠ 0}))) := by -- --- PROOF ---
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `[0, 0]`: nothing to invert
    rintro ⟨rfl, rfl⟩
    refine Set.eq_empty_of_forall_notMem fun v ⟨y, ⟨hy, hy0⟩, _⟩ => hy0 ?_
    exact le_antisymm hy.2 hy.1
  · -- away from `0`: falling, so the ends swap
    intro h
    have h0 : ∀ y ∈ Set.Icc lo hi, y ≠ 0 := fun y hy hy0 => by
      rcases h with h | h <;> [linarith [hy.1]; linarith [hy.2]]
    have hanti : AntitoneOn (·⁻¹ : ℝ → ℝ) (Set.Icc lo hi) := fun x hx y hy hxy => by
      rcases h with h | h
      · exact (inv_le_inv₀ (by linarith [hy.1]) (by linarith [hx.1])).2 hxy
      · exact (inv_le_inv_of_neg (by linarith [hy.2]) (by linarith [hx.2])).2 hxy
    have hset : Set.Icc lo hi ∩ {y | y ≠ 0} = Set.Icc lo hi := Set.inter_eq_left.2 h0
    rw [hset, (continuousOn_inv₀.mono fun y hy => h0 y hy).image_Icc_of_antitoneOn hle hanti]
  · -- `0` at the lower end
    rintro ⟨rfl, h⟩
    exact aux_inv_image_Ioc hi h
  · -- `0` at the upper end, by symmetry
    rintro ⟨h, rfl⟩
    have hs := aux_inv_image_Ioc (-lo) (by linarith)
    ext v
    constructor
    · rintro ⟨y, ⟨hy, hy0⟩, rfl⟩
      have := hs.subset ⟨-y, ⟨⟨by linarith [hy.2], by linarith [hy.1]⟩, neg_ne_zero.2 hy0⟩, rfl⟩
      simp only [Set.mem_Ici, inv_neg, neg_le_neg_iff] at this
      exact this
    · -- a value below `1/lo` comes from its negation's preimage
      intro hv
      obtain ⟨y, ⟨hy, hy0⟩, hyv⟩ := hs.symm.subset (show -v ∈ Set.Ici (-lo)⁻¹ by
        simp only [Set.mem_Ici, inv_neg, neg_le_neg_iff]; exact hv)
      refine ⟨-y, ⟨⟨by linarith [hy.2], by linarith [hy.1]⟩, neg_ne_zero.2 hy0⟩, ?_⟩
      simp only [inv_neg] at hyv ⊢
      linarith
  · -- `0` inside: both half-lines, unbounded
    rintro ⟨hl, hh⟩
    have hs := aux_inv_image_Ioc hi hh
    have hsub : Set.Icc 0 hi ∩ {y | y ≠ 0} ⊆ Set.Icc lo hi ∩ {y | y ≠ 0} :=
      fun y ⟨hy, hy0⟩ => ⟨⟨by linarith [hy.1], hy.2⟩, hy0⟩
    have hn := aux_inv_image_Ioc (-lo) (by linarith)
    have hsub' : ∀ y ∈ Set.Icc 0 (-lo) ∩ {y | y ≠ 0}, -y ∈ Set.Icc lo hi ∩ {y | y ≠ 0} :=
      fun y ⟨hy, hy0⟩ => ⟨⟨by linarith [hy.2], by linarith [hy.1]⟩, neg_ne_zero.2 hy0⟩
    constructor
    · -- above any bound, just right of `0`
      rintro ⟨M, hM⟩
      obtain ⟨y, hy, hyv⟩ := hs.symm.subset (show max M hi⁻¹ + 1 ∈ Set.Ici hi⁻¹ by
        simp only [Set.mem_Ici]; linarith [le_max_right M hi⁻¹])
      have := hM ⟨y, hsub hy, hyv⟩
      linarith [le_max_left M hi⁻¹]
    · -- below any bound, just left of `0`
      rintro ⟨M, hM⟩
      obtain ⟨y, hy, hyv⟩ := hn.symm.subset (show max (-M) (-lo)⁻¹ + 1 ∈ Set.Ici (-lo)⁻¹ by
        simp only [Set.mem_Ici]; linarith [le_max_right (-M) (-lo)⁻¹])
      have := hM ⟨-y, hsub' y hy, rfl⟩
      have hm := le_max_left (-M) (-lo)⁻¹
      simp only [inv_neg] at this hyv hm
      linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

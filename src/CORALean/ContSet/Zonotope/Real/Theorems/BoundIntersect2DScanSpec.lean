import CORALean.ContSet.Zonotope.Real.Operations.BoundIntersect2DScan
import CORALean.ContSet.Zonotope.Real.Theorems.ScanFold
import CORALean.ContSet.Zonotope.Real.Theorems.SectionEqIccWalkEdges
import CORALean.ContSet.Zonotope.Real.Theorems.CornerEqBottomAdd
import CORALean.ContSet.Zonotope.Real.Theorems.SumFlipCompl
import CORALean.ContSet.Zonotope.Real.Theorems.CornerSuccAdd
import CORALean.ContSet.Zonotope.Real.Theorems.CornerNotSuccSub
import CORALean.ContSet.Zonotope.Real.Theorems.ConstructPointUp
import CORALean.ContSet.Zonotope.Real.Theorems.ConstructCompPerm
import CORALean.ContSet.Zonotope.Real.Theorems.CrossNonnegOfArgLe
import CORALean.ContSet.Zonotope.Real.Theorems.PointUpHalfPlane

/-!
# [1, Alg. 3] returns the section of the zonogon

`{γ} × [m; M] = Z ∩ L_γ`, as printed, for a zonogon with at least one generator. After the
generators are turned upward and sorted by angle, the edges `[P; P ± 2g]` the two loops scan are
those of `Zonotope.walkEdges`: the first loop the first block of the walk, the second the second.
`scan_fold` says `m` and `M` are the extremes of the `y` at which those edges meet `L_γ`, and
`section_eq_Icc_walkEdges` that the section is the interval between the extremes. `m = ∞`,
`M = -∞` is the empty section.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The first loop's vertices are the first block of the walk. -/
theorem Zonotope.aux_up_vertex (Z : Zonotope (Vec ℝ 2)) (k : Fin Z.h) :
    (Z.c - ∑ j, Z.G j) + (∑ i, if i < k then (2 : ℝ) • Z.G i else 0)
      = Z.corner (fun j => decide (j.val < k.val)) := by -- --- PROOF ---
  rw [Zonotope.corner_eq_bottom_add, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i < k
  · simp [h, Fin.lt_def.mp h]
  · simp [h]

/-- The second loop's vertices are the second block of the walk. -/
theorem Zonotope.aux_down_vertex (Z : Zonotope (Vec ℝ 2)) (k : Fin Z.h) :
    ((Z.c - ∑ j, Z.G j) + ∑ i, (2 : ℝ) • Z.G i)
        + (∑ i, if i < k then -((2 : ℝ) • Z.G i) else 0)
      = Z.corner (fun j => !decide (j.val < k.val)) := by -- --- PROOF ---
  have hc := Zonotope.sum_flip_compl Z (fun j => decide (j.val < k.val))
  have hF : (∑ i, if i < k then -((2 : ℝ) • Z.G i) else 0)
      = -((2 : ℝ) • ∑ j, if decide (j.val < k.val) = true then Z.G j else 0) := by
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i < k
    · simp [h, Fin.lt_def.mp h]
    · simp [h]
  rw [Zonotope.corner_eq_bottom_add, hF, ← Finset.smul_sum, ← hc]
  module

/-- The two loops, on a sorted zonogon with the generators upward, end with the section's ends. -/
theorem Zonotope.aux_scan_sorted (Z : Zonotope (Vec ℝ 2)) (hh : 0 < Z.h)
    (h1 : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0))
    (h2 : ∀ i j : Fin Z.h, i < j → 0 ≤ Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0) (γ : ℝ)
    (P₀ : Vec ℝ 2) (hP₀ : P₀ = Z.c - ∑ j, Z.G j) (up down : Vec ℝ 2 × EReal × EReal)
    (hup : Fin.foldl Z.h (fun s j => (s.1 + (2 : ℝ) • Z.G j,
      Zonotope.scanEdge γ s.1 (s.1 + (2 : ℝ) • Z.G j) s.2)) (P₀, ((⊤ : EReal), (⊥ : EReal))) = up)
    (hdown : Fin.foldl Z.h (fun s j => (s.1 - (2 : ℝ) • Z.G j,
      Zonotope.scanEdge γ s.1 (s.1 - (2 : ℝ) • Z.G j) s.2)) up = down) :
    {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ Z.construct}
      = {y : ℝ | down.2.1 ≤ y ∧ (y : EReal) ≤ down.2.2} := by -- --- PROOF ---
  obtain ⟨u1, u2, u3, uA, uB, uC⟩ := Zonotope.scan_fold γ (fun j => (2 : ℝ) • Z.G j)
    (fun P j => P + (2 : ℝ) • Z.G j) (fun _ _ => rfl) P₀ (⊤, ⊥) up hup
  obtain ⟨d1, d2, d3, dA, dB, dC⟩ := Zonotope.scan_fold γ (fun j => -((2 : ℝ) • Z.G j))
    (fun P j => P - (2 : ℝ) • Z.G j) (fun P j => sub_eq_add_neg _ _) up.1 up.2 down hdown
  -- the edges of the two loops are the walk's, block by block
  have hE1 : ∀ k : Fin Z.h, (P₀ + ∑ i, if i < k then (2 : ℝ) • Z.G i else 0)
      = Z.corner (fun j => decide (j.val < k.val)) := fun k => by
    rw [hP₀]; exact Zonotope.aux_up_vertex Z k
  have hE2 : ∀ k : Fin Z.h, (up.1 + ∑ i, if i < k then -((2 : ℝ) • Z.G i) else 0)
      = Z.corner (fun j => !decide (j.val < k.val)) := fun k => by
    rw [u1, hP₀]; exact Zonotope.aux_down_vertex Z k
  have hfirst : ∀ (k : Fin Z.h) (y : ℝ), (![γ, y] : Vec ℝ 2) ∈ segment ℝ
      (P₀ + ∑ i, if i < k then (2 : ℝ) • Z.G i else 0)
      (P₀ + (∑ i, if i < k then (2 : ℝ) • Z.G i else 0) + (2 : ℝ) • Z.G k) ↔
      (![γ, y] : Vec ℝ 2) ∈ segment ℝ (Z.corner fun j => decide (j.val < k.val))
        (Z.corner fun j => decide (j.val < k.val + 1)) := fun k y => by
    rw [hE1 k, Zonotope.corner_succ_add]
  have hsecond : ∀ (k : Fin Z.h) (y : ℝ), (![γ, y] : Vec ℝ 2) ∈ segment ℝ
      (up.1 + ∑ i, if i < k then -((2 : ℝ) • Z.G i) else 0)
      (up.1 + (∑ i, if i < k then -((2 : ℝ) • Z.G i) else 0) + -((2 : ℝ) • Z.G k)) ↔
      (![γ, y] : Vec ℝ 2) ∈ segment ℝ (Z.corner fun j => !decide (j.val < k.val))
        (Z.corner fun j => !decide (j.val < k.val + 1)) := fun k y => by
    rw [hE2 k, Zonotope.corner_not_succ_sub]
  -- every point of a walk edge on the line is between `m` and `M`
  have hbound : ∀ y : ℝ, (![γ, y] : Vec ℝ 2) ∈ Z.walkEdges →
      down.2.1 ≤ y ∧ (y : EReal) ≤ down.2.2 := by
    intro y hy
    obtain ⟨k, hk | hk⟩ := (Z.mem_walkEdges_iff _).mp hy
    · obtain ⟨a, b⟩ := uA k y ((hfirst k y).mpr hk)
      exact ⟨d2.trans a, b.trans d3⟩
    · exact dA k y ((hsecond k y).mpr hk)
  -- and `m` and `M` are such points, unless nothing meets
  have hattain : (down.2.1 = ⊤ ∨ ∃ y : ℝ, (![γ, y] : Vec ℝ 2) ∈ Z.walkEdges ∧ down.2.1 = y)
      ∧ (down.2.2 = ⊥ ∨ ∃ y : ℝ, (![γ, y] : Vec ℝ 2) ∈ Z.walkEdges ∧ down.2.2 = y) := by
    constructor
    · rcases dB with h | ⟨k, y, hy, h⟩
      · rcases uB with h' | ⟨k, y, hy, h'⟩
        · exact Or.inl (h.trans h')
        · exact Or.inr ⟨y, (Z.mem_walkEdges_iff _).mpr ⟨k, Or.inl ((hfirst k y).mp hy)⟩,
            h.trans h'⟩
      · exact Or.inr ⟨y, (Z.mem_walkEdges_iff _).mpr ⟨k, Or.inr ((hsecond k y).mp hy)⟩, h⟩
    · rcases dC with h | ⟨k, y, hy, h⟩
      · rcases uC with h' | ⟨k, y, hy, h'⟩
        · exact Or.inl (h.trans h')
        · exact Or.inr ⟨y, (Z.mem_walkEdges_iff _).mpr ⟨k, Or.inl ((hfirst k y).mp hy)⟩,
            h.trans h'⟩
      · exact Or.inr ⟨y, (Z.mem_walkEdges_iff _).mpr ⟨k, Or.inr ((hsecond k y).mp hy)⟩, h⟩
  -- the section is an interval between two such points, or empty
  ext y
  simp only [Set.mem_setOf_eq]
  by_cases hne : ∃ y, (![γ, y] : Vec ℝ 2) ∈ Z.construct
  -- a nonempty section, `[yl; yh]` by the section theorem
  · obtain ⟨yl, yh, hyl, hyh, hS⟩ := Z.section_eq_Icc_walkEdges hh h1 h2 γ hne
    have hy : ∀ y' : ℝ, (![γ, y'] : Vec ℝ 2) ∈ Z.construct ↔ yl ≤ y' ∧ y' ≤ yh := fun y' => by
      rw [← Set.mem_Icc, ← hS]; rfl
    rw [hy y]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨(hbound yl hyl).1.trans (EReal.coe_le_coe_iff.mpr a),
        (EReal.coe_le_coe_iff.mpr b).trans (hbound yh hyh).2⟩
    -- between `m` and `M`, so in the section
    · rintro ⟨a, b⟩
      -- `m` and `M` are attained at points of the section
      obtain ⟨ym, hym, hm⟩ : ∃ ym : ℝ, (![γ, ym] : Vec ℝ 2) ∈ Z.walkEdges ∧ down.2.1 = ym := by
        rcases hattain.1 with h | h
        · rw [h] at a; exact absurd a (by simp)
        · exact h
      obtain ⟨yM, hyM, hM⟩ : ∃ yM : ℝ, (![γ, yM] : Vec ℝ 2) ∈ Z.walkEdges ∧ down.2.2 = yM := by
        rcases hattain.2 with h | h
        · rw [h] at b; exact absurd b (by simp)
        · exact h
      have h3 : (![γ, ym] : Vec ℝ 2) ∈ Z.construct := Z.walkEdges_subset_construct hym
      have h4 : (![γ, yM] : Vec ℝ 2) ∈ Z.construct := Z.walkEdges_subset_construct hyM
      rw [hy] at h3 h4
      rw [hm] at a
      rw [hM] at b
      exact ⟨h3.1.trans (EReal.coe_le_coe_iff.mp a), (EReal.coe_le_coe_iff.mp b).trans h4.2⟩
  · -- nothing in the section, so nothing meets, and `m = ∞`
    refine ⟨fun h => absurd ⟨y, h⟩ hne, fun ⟨a, b⟩ => ?_⟩
    rcases hattain.1 with h | ⟨ym, hym, hm⟩
    · rw [h] at a; exact absurd a (by simp)
    · exact absurd ⟨ym, Z.walkEdges_subset_construct hym⟩ hne


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.boundIntersect2DScan_spec (Z : Zonotope (Vec ℝ 2)) (hh : 0 < Z.h) (γ : ℝ) :
    {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ Z.construct} =
      {y : ℝ | (Z.boundIntersect2DScan γ).1 ≤ y ∧
        (y : EReal) ≤ (Z.boundIntersect2DScan γ).2} := by -- --- PROOF ---
  -- the zonogon with the generators turned upward, then sorted by angle
  set π := Tuple.sort fun i => Complex.arg (⟨Z.pointUp.G i 0, Z.pointUp.G i 1⟩ : ℂ) with hπ
  have h1 : ∀ j, 0 ≤ (⟨Z.pointUp.h, Z.pointUp.c, Z.pointUp.G ∘ π⟩ : Zonotope (Vec ℝ 2)).G j 1 ∧
      (0 < (⟨Z.pointUp.h, Z.pointUp.c, Z.pointUp.G ∘ π⟩ : Zonotope (Vec ℝ 2)).G j 1 ∨
        0 ≤ (⟨Z.pointUp.h, Z.pointUp.c, Z.pointUp.G ∘ π⟩ : Zonotope (Vec ℝ 2)).G j 0) :=
    fun j => Z.pointUp_half_plane (π j)
  have h2 : ∀ i j : Fin Z.pointUp.h, i < j → 0 ≤
      (⟨Z.pointUp.h, Z.pointUp.c, Z.pointUp.G ∘ π⟩ : Zonotope (Vec ℝ 2)).G i 0 *
          (⟨Z.pointUp.h, Z.pointUp.c, Z.pointUp.G ∘ π⟩ : Zonotope (Vec ℝ 2)).G j 1 -
        (⟨Z.pointUp.h, Z.pointUp.c, Z.pointUp.G ∘ π⟩ : Zonotope (Vec ℝ 2)).G i 1 *
          (⟨Z.pointUp.h, Z.pointUp.c, Z.pointUp.G ∘ π⟩ : Zonotope (Vec ℝ 2)).G j 0 :=
    fun i j hij => Zonotope.cross_nonneg_of_arg_le (Z.pointUp_half_plane (π i)).1
      (Tuple.monotone_sort (fun i => Complex.arg (⟨Z.pointUp.G i 0, Z.pointUp.G i 1⟩ : ℂ))
        hij.le)
  rw [← Z.construct_pointUp, ← Z.pointUp.construct_comp_perm π]
  refine Zonotope.aux_scan_sorted ⟨Z.pointUp.h, Z.pointUp.c, Z.pointUp.G ∘ π⟩ hh h1 h2 γ _ ?_
    _ _ rfl rfl
  show _ = Z.pointUp.c - ∑ j, Z.pointUp.G (π j)
  rw [Equiv.sum_comp π Z.pointUp.G]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

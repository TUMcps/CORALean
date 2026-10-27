module

public import CORALean.ContSet.Zonotope.Real.Theorems.CrossSupport
public import CORALean.ContSet.Zonotope.Real.Theorems.EdgePointLeast
public import CORALean.ContSet.Zonotope.Real.Theorems.SegmentMeetsVlineIff
public import CORALean.ContSet.Zonotope.Real.Theorems.CornerMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.CornerEqBottom
public import CORALean.ContSet.Zonotope.Real.Theorems.CrossNegOfHorizontal
public import CORALean.ContSet.Zonotope.Real.Theorems.CornerBottomLe
public import CORALean.ContSet.Zonotope.Real.Theorems.ReachLe
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Segment
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# The lowest point of a section lies on an edge of the walk

The core of [1, Alg. 3] and [1, Alg. 4]. Take generators in the upper half-plane and an order `r`
on them with `σ·cross(g_i, g_j) ≥ 0` for `r i < r j`, `σ = ±1`: increasing angle for `σ = 1`,
decreasing for `σ = -1`. From the lowest corner the walk adds `2 g` along `r`, and at the generators
pointing along `σ` in `x` it moves monotonically towards the line `x = γ`. The first step that
reaches it is an edge `[P_a; P_a + 2 g_a]`, the zonogon is on one side of its line
(`Zonotope.cross_support`), and the point of the edge on `x = γ` is the lowest point of the
section. It needs `γ` on the walk's side of the lowest corner, `0 ≤ σ (γ - P₀)`.

## Inputs
* `Z` – planar zonotope
* `σ` – orientation sign
* `r` – generator ranking
* `γ` – abscissa of the vertical line

## Hypotheses
* `hh` – at least one generator
* `hH` – generators point upward
* `hσ` – `σ` is plus or minus one
* `hr` – ranking injective
* `hord` – ranking sorts generators by angle
* `hγ` – line right of the bottom corner
* `hne` – line meets `Z`

## Conclusion
* the least point on the line lies on an edge of the walk

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The first index whose cumulative weight passes `τ`, among those carrying weight. -/
private theorem Zonotope.aux_pick {ι : Type} [Fintype ι] (r : ι → ℤ) (hr : Function.Injective r)
    (ω : ι → ℝ) (A : Finset ι) (hA : A.Nonempty) (hω : ∀ j, j ∉ A → ω j = 0) {τ : ℝ}
    (h0 : 0 ≤ τ) (hW : τ ≤ ∑ j, ω j) : -- --- CONCL ---
    ∃ a ∈ A, (∑ j, if r j < r a then ω j else 0) ≤ τ ∧
      τ ≤ (∑ j, if r j < r a then ω j else 0) + ω a := by -- --- PROOF ---
  classical
  set S : ι → ℝ := fun a => ∑ j, if r j ≤ r a then ω j else 0 with hS
  set pre : ι → ℝ := fun a => ∑ j, if r j < r a then ω j else 0 with hpre
  -- the greatest index reaches everything
  obtain ⟨astar, hastarA, hastar⟩ := Finset.exists_max_image A r hA
  have hSstar : ∑ j, ω j ≤ S astar := by
    refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
    by_cases hj : j ∈ A
    · rw [if_pos (hastar j hj)]
    · rw [hω j hj]; simp
  -- the first one whose cumulative weight passes `τ`
  set T : Finset ι := A.filter (fun a => τ ≤ S a) with hT
  have hTne : T.Nonempty := ⟨astar, by simp [hT, hastarA]; linarith⟩
  obtain ⟨a, haT, hamin⟩ := Finset.exists_min_image T r hTne
  have haA : a ∈ A := (Finset.mem_filter.mp haT).1
  have haS : τ ≤ S a := (Finset.mem_filter.mp haT).2
  -- its cumulative weight is the weight before it and its own
  have hS_eq : S a = pre a + ω a := by
    have : ∀ j, (if r j ≤ r a then ω j else 0) = (if r j < r a then ω j else 0)
        + (if j = a then ω j else 0) := fun j => by
      by_cases h1 : r j < r a
      · have : j ≠ a := fun h => by rw [h] at h1; exact lt_irrefl _ h1
        simp [h1, this, h1.le]
      · by_cases h2 : j = a
        · subst h2; simp
        · have : ¬ r j ≤ r a := fun h => h2 (hr (le_antisymm h (not_lt.mp h1)))
          simp [h1, h2, this]
    simp only [hS, hpre, this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  refine ⟨a, haA, ?_, by rw [← hS_eq]; exact haS⟩
  -- the weight before it does not pass `τ`, or the index just before would have been first
  by_contra hlt
  push Not at hlt
  have hB : (A.filter (fun j => r j < r a)).Nonempty := by
    by_contra hB
    rw [Finset.not_nonempty_iff_eq_empty] at hB
    have : pre a = 0 := Finset.sum_eq_zero fun j _ => by
      by_cases h : r j < r a
      · have : j ∉ A := fun hj => by
          have : j ∈ A.filter (fun j => r j < r a) := Finset.mem_filter.mpr ⟨hj, h⟩
          rw [hB] at this; simp at this
        rw [if_pos h, hω j this]
      · rw [if_neg h]
    linarith
  -- the index just before it would have been first, so it is the greatest before
  obtain ⟨a', ha'B, ha'max⟩ := Finset.exists_max_image _ r hB
  have ha'A : a' ∈ A := (Finset.mem_filter.mp ha'B).1
  have ha'lt : r a' < r a := (Finset.mem_filter.mp ha'B).2
  have hSa' : S a' = pre a := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ A
    · have : r j ≤ r a' ↔ r j < r a := ⟨fun h => lt_of_le_of_lt h ha'lt, fun h =>
        ha'max j (Finset.mem_filter.mpr ⟨hj, h⟩)⟩
      simp only [this]
    · rw [hω j hj]; simp
  have : a' ∈ T := Finset.mem_filter.mpr ⟨ha'A, by rw [hSa']; exact hlt.le⟩
  exact absurd (hamin a' this) (not_le.mpr ha'lt)

/-- The corner after `a` is the corner before it plus `2 g_a`. -/
private theorem Zonotope.aux_step (Z : Zonotope (Vec ℝ 2)) {r : Fin Z.h → ℤ}
    (hr : Function.Injective r) (a : Fin Z.h) (k : Fin 2) : -- --- CONCL ---
    Z.corner (fun j => decide (r j ≤ r a)) k
      = Z.corner (fun j => decide (r j < r a)) k + 2 * Z.G a k := by -- --- PROOF ---
  classical
  rw [Zonotope.corner_eq_bottom, Zonotope.corner_eq_bottom (s := fun j => decide (r j < r a))]
  have : ∀ j, (if decide (r j ≤ r a) = true then Z.G j k else 0)
      = (if decide (r j < r a) = true then Z.G j k else 0) + (if j = a then Z.G j k else 0) :=
    fun j => by
      by_cases h1 : r j < r a
      · have : j ≠ a := fun h => by rw [h] at h1; exact lt_irrefl _ h1
        simp [h1, this, h1.le]
      · by_cases h2 : j = a
        · subst h2; simp
        · have : ¬ r j ≤ r a := fun h => h2 (hr (le_antisymm h (not_lt.mp h1)))
          simp [h1, h2, this]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The abscissa of the corner before `a`, along `σ`, is the lowest corner's plus the weight before
it, when no generator before `a` points against `σ`. -/
private theorem Zonotope.aux_prefix_abscissa (Z : Zonotope (Vec ℝ 2)) (σ : ℝ) (r : Fin Z.h → ℤ)
    (a : Fin Z.h) (hpred : ∀ j, r j < r a → 0 ≤ σ * Z.G j 0) : -- --- CONCL ---
    σ * Z.corner (fun j => decide (r j < r a)) 0
      = σ * Z.corner (fun _ => false) 0
        + ∑ j, if r j < r a then 2 * max (σ * Z.G j 0) 0 else 0 := by -- --- PROOF ---
  classical
  rw [Zonotope.corner_eq_bottom, mul_add]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : r j < r a
  · simp only [h, decide_true, if_true, max_eq_left (hpred j h)]
    ring
  · simp [h]


/-- The edge `[P_a; P_a + 2 g_a]` meets the line, and its point there is the lowest of the section,
when the line is between the ends of the edge along `σ`. -/
private theorem Zonotope.aux_edge (Z : Zonotope (Vec ℝ 2)) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {r : Fin Z.h → ℤ} (hr : Function.Injective r)
    (hord : ∀ i j, r i < r j → 0 ≤ σ * (Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0)) (γ : ℝ)
    (a : Fin Z.h) (haX : 0 < σ * Z.G a 0)
    (hlo : 0 ≤ σ * (γ - Z.corner (fun j => decide (r j < r a)) 0))
    (hhi : σ * (γ - Z.corner (fun j => decide (r j < r a)) 0) ≤
      2 * (σ * Z.G a 0)) : -- --- CONCL ---
    ∃ y : ℝ,
      (![γ, y] : Vec ℝ 2) ∈ segment ℝ (Z.corner fun j => decide (r j < r a))
        (Z.corner fun j => decide (r j ≤ r a)) ∧
      (![γ, y] : Vec ℝ 2) ∈ Z.construct ∧
      ∀ y', (![γ, y'] : Vec ℝ 2) ∈ Z.construct → y ≤ y' := by -- --- PROOF ---
  classical
  -- the far end of the edge is `P_a + 2 g_a`
  have hQP : Z.corner (fun j => decide (r j ≤ r a))
      = Z.corner (fun j => decide (r j < r a)) + (2 : ℝ) • Z.G a := by
    ext k
    simpa using Zonotope.aux_step Z hr a k
  rw [hQP]
  -- the line is between the abscissae of the ends, so it meets the edge
  set Pa := Z.corner (fun j => decide (r j < r a)) with hPa
  have hmeet : min (Pa 0) ((Pa + (2 : ℝ) • Z.G a) 0) ≤ γ ∧
      γ ≤ max (Pa 0) ((Pa + (2 : ℝ) • Z.G a) 0) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hσ with rfl | rfl
    · exact ⟨min_le_of_left_le (by linarith), le_max_of_le_right (by linarith)⟩
    · exact ⟨min_le_of_right_le (by linarith), le_max_of_le_left (by linarith)⟩
  obtain ⟨z, hz, hzx⟩ := (Zonotope.segment_meets_vline_iff _ _ γ).mpr hmeet
  -- and the zonogon is on one side of the edge's line
  obtain ⟨hzZ, hzmin⟩ := Z.edge_point_least σ (fun j => decide (r j < r a)) a (by simp)
    (fun b hb => hord b a (by simpa using hb))
    (fun c hc hca => hord a c (lt_of_le_of_ne (not_lt.mp (by simpa using hc))
      (fun h => hca (hr h.symm)))) haX hz
  have hz' : (![γ, z 1] : Vec ℝ 2) = z := by
    ext k; fin_cases k
    · exact hzx.symm
    · rfl
  exact ⟨z 1, by rw [hz']; exact hz, by rw [hz']; exact hzZ,
    fun y' hy' => hzmin y' (by rwa [hzx])⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.exists_edge_least_section (Z : Zonotope (Vec ℝ 2)) (hh : 0 < Z.h)
    (hH : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0)) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {r : Fin Z.h → ℤ} (hr : Function.Injective r)
    (hord : ∀ i j, r i < r j → 0 ≤ σ * (Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0)) (γ : ℝ)
    (hγ : 0 ≤ σ * (γ - Z.corner (fun _ => false) 0))
    (hne : ∃ y, (![γ, y] : Vec ℝ 2) ∈ Z.construct) : -- --- CONCL ---
    ∃ a : Fin Z.h, ∃ y : ℝ,
      (![γ, y] : Vec ℝ 2) ∈ segment ℝ (Z.corner fun j => decide (r j < r a))
        (Z.corner fun j => decide (r j ≤ r a)) ∧
      (![γ, y] : Vec ℝ 2) ∈ Z.construct ∧
      ∀ y', (![γ, y'] : Vec ℝ 2) ∈ Z.construct → y ≤ y' := by -- --- PROOF ---
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  set P0 := Z.corner (fun _ => false) with hP0
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hbot := fun z (hz : z ∈ Z.construct) => Z.corner_bottom_le (fun j => (hH j).1) hz
  by_cases hA : ∃ a, 0 < σ * Z.G a 0
  swap
  · -- no right-pointing generator: the lowest corner is on the line
    push Not at hA
    have hsum : ∑ j, 2 * max (σ * Z.G j 0) 0 = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [max_eq_right (hA j)]; ring
    have h1 : σ * (γ - P0 0) ≤ 0 := hsum ▸ Z.reach_le σ hy₀
    have hγ0 : γ = P0 0 := by
      have := (mul_eq_zero.mp (le_antisymm h1 hγ)).resolve_left hσne
      linarith
    obtain ⟨a0, -, ha0⟩ := Finset.exists_min_image Finset.univ r
      ⟨⟨0, hh⟩, Finset.mem_univ _⟩
    have hs : (fun j => decide (r j < r a0)) = fun _ => false :=
      funext fun j => by simp [not_lt.mpr (ha0 j (Finset.mem_univ j))]
    have hpt : (![γ, P0 1] : Vec ℝ 2) = P0 := by
      ext k; fin_cases k
      · exact hγ0
      · rfl
    refine ⟨a0, P0 1, ?_, ?_, fun y' hy' => hbot _ hy'⟩
    · rw [hpt, hs]
      exact left_mem_segment ℝ _ _
    · rw [hpt]
      exact Z.corner_mem_construct _
  -- the first right-pointing generator whose cumulative reach passes the line
  set ω : Fin Z.h → ℝ := fun j => 2 * max (σ * Z.G j 0) 0 with hω
  set τ : ℝ := σ * (γ - P0 0) with hτ
  set A : Finset (Fin Z.h) := Finset.univ.filter (fun a => 0 < σ * Z.G a 0) with hAdef
  have hωA : ∀ j, j ∉ A → ω j = 0 := fun j hj => by
    simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
    simp [hω, max_eq_right hj]
  obtain ⟨a0, ha0⟩ := hA
  obtain ⟨a, haA, hpre_le, hτ_le⟩ := Zonotope.aux_pick r hr ω A ⟨a0, by simp [hAdef, ha0]⟩ hωA
    hγ (Z.reach_le σ hy₀)
  set pre : ℝ := ∑ j, if r j < r a then ω j else 0 with hpre
  have haX : 0 < σ * Z.G a 0 := by simpa [hAdef] using haA
  have hωa : ω a = 2 * (σ * Z.G a 0) := by simp [hω, max_eq_left haX.le]
  -- generators before `a` do not point against `σ`
  have hpred : ∀ j, r j < r a → 0 ≤ σ * Z.G j 0 := fun j hj => by
    by_contra hneg
    push Not at hneg
    have h1 := Zonotope.cross_neg_of_horizontal hσ (hH j) (hH a) haX hneg
    have h2 := hord j a hj
    linarith
  set Pa := Z.corner (fun j => decide (r j < r a)) with hPa
  set Qa := Z.corner (fun j => decide (r j ≤ r a)) with hQa
  have hQP : ∀ k, Qa k = Pa k + 2 * Z.G a k := Zonotope.aux_step Z hr a
  have hPx : σ * Pa 0 = σ * P0 0 + pre := Zonotope.aux_prefix_abscissa Z σ r a hpred
  -- the line `x = γ` cuts the edge `[Pa; Qa]`
  have hτpre : σ * (γ - Pa 0) = τ - pre := by rw [hτ]; linarith
  obtain ⟨y, hy⟩ := Zonotope.aux_edge Z hσ hr hord γ a haX (by rw [hτpre]; linarith)
    (by rw [hτpre]; linarith [hωa])
  exact ⟨a, y, hy⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

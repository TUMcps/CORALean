module

public import CORALean.ContSet.HPolytope.Real.Operations.TightAt
public import CORALean.ContSet.HPolytope.Real.Operations.BasicPoint
public import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
public import CORALean.ContSet.HPolytope.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Positivity
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import Mathlib.Analysis.Convex.KreinMilman
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope

@[expose] public section

/-!
# Halfspaces to vertices

`HPolytope.vPolytope_contains`: its `vPolytope` contains it.

## Inputs
* `P` – halfspace polytope

## Hypotheses
* `hc` – polytope compact
* `hne` – polytope nonempty

## Conclusion
* polytope is contained in its vertex polytope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n : ℕ}

/-- Extreme points of a halfspace description. -/
private theorem HPolytope.aux_eq_zero_of_extremePoint (P : HPolytope (Vec ℝ n)) {x : Vec ℝ n}
    (hx : x ∈ P.construct.extremePoints ℝ) {d : Vec ℝ n}
    (htight : ∀ i, P.A i x = P.b i → P.A i d = 0) (heq : ∀ i, P.Ae i d = 0) : -- --- CONCL ---
    d = 0 := by -- --- PROOF ---
  by_contra hd
  have hxmem : x ∈ P.construct := hx.1
  -- the rows with slack at `x` still have slack nearby
  have hUopen : IsOpen (⋂ i, {y : Vec ℝ n | P.A i x < P.b i → P.A i y < P.b i}) := by
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases h : P.A i x < P.b i
    · simp only [h, true_implies]
      exact isOpen_lt (P.A i).continuous_of_finiteDimensional continuous_const
    · simp only [h, false_implies, Set.setOf_true]
      exact isOpen_univ
  have hxU : x ∈ ⋂ i, {y : Vec ℝ n | P.A i x < P.b i → P.A i y < P.b i} :=
    Set.mem_iInter.mpr fun _ h => h
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hUopen x hxU
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have ht : 0 < δ / (2 * ‖d‖) := div_pos hδ (by positivity)
  -- a step of that size along `d` stays inside every row, tight or slack
  have hstep : ∀ ε : ℝ, |ε| = δ / (2 * ‖d‖) → x + ε • d ∈ P.construct := by
    intro ε hε
    have hnorm : |ε| * ‖d‖ = δ / 2 := by
      rw [hε]
      field_simp
    have hdist : dist (x + ε • d) x < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hnorm]
      linarith
    have hmem := hball (Metric.mem_ball.mpr hdist)
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases h : P.A i x = P.b i
      · refine le_of_eq ?_
        rw [map_add, map_smul, htight i h, smul_eq_mul, mul_zero, add_zero, h]
      · exact le_of_lt (Set.mem_iInter.mp hmem i (lt_of_le_of_ne (hxmem.1 i) h))
    · rw [map_add, map_smul, heq i, smul_eq_mul, mul_zero, add_zero]
      exact hxmem.2 i
  -- so `x` lies in the open segment between two points of `P`, which it cannot
  have hup : x + (δ / (2 * ‖d‖)) • d ∈ P.construct := hstep _ (abs_of_pos ht)
  have hdown : x + (-(δ / (2 * ‖d‖))) • d ∈ P.construct :=
    hstep _ (by rw [abs_neg, abs_of_pos ht])
  have hseg : x ∈ openSegment ℝ (x + (-(δ / (2 * ‖d‖))) • d) (x + (δ / (2 * ‖d‖)) • d) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, ← add_smul]
    norm_num
  obtain ⟨hfix, -⟩ := (mem_extremePoints.mp hx).2 _ hdown _ hup hseg
  have hzero : (-(δ / (2 * ‖d‖))) • d = 0 := by
    have h : x + (-(δ / (2 * ‖d‖))) • d - x = x - x := by rw [hfix]
    simpa using h
  rcases smul_eq_zero.mp hzero with h | h
  · rw [neg_eq_zero] at h
    linarith
  · exact hd h

end


/-- The soundness half of vertex enumeration: a list holding every point the
rows pin down encloses the polytope. An implementation must then show it found
those points, never that its search was exhaustive in any other sense. -/
private theorem HPolytope.aux_contains_of_pinned (hc : IsCompact P.construct)
    (W : VPolytope (Vec ℝ n)) (hW : ∀ x ∈ P.construct,
        (∀ d : Vec ℝ n, (∀ i, P.A i x = P.b i → P.A i d = 0) → (∀ i, P.Ae i d = 0) → d = 0) →
        x ∈ Set.range W.V) : -- --- CONCL ---
    P.construct ⊆ W.construct := by -- --- PROOF ---
  have hext : P.construct.extremePoints ℝ ⊆ Set.range W.V := fun x hx =>
    hW x hx.1 fun _ h₁ h₂ => P.aux_eq_zero_of_extremePoint hx h₁ h₂
  have hclosed : IsClosed (convexHull ℝ (Set.range W.V)) :=
    (Set.Finite.isCompact_convexHull ℝ (Set.finite_range W.V)).isClosed
  calc P.construct = closure (convexHull ℝ (P.construct.extremePoints ℝ)) :=
        (closure_convexHull_extremePoints hc P.convex_construct).symm
    _ ⊆ closure (convexHull ℝ (Set.range W.V)) := closure_mono (convexHull_mono hext)
    _ = convexHull ℝ (Set.range W.V) := hclosed.closure_eq
    _ = W.construct := W.construct_eq_convexHull.symm


section
variable {n : ℕ}

/-- A point no direction is free at is the one its own tight rows name. -/
private theorem HPolytope.aux_basicPoint_tightAt (P : HPolytope (Vec ℝ n)) {x : Vec ℝ n}
    (hx : x ∈ P.construct)
    (hpin : ∀ d : Vec ℝ n, (∀ i, P.A i x = P.b i → P.A i d = 0) → (∀ i, P.Ae i d = 0) → d = 0)
    : -- --- CONCL ---
    P.basicPoint (P.tightAt x) = x := by -- --- PROOF ---
  have hspec : ∀ y : Vec ℝ n,
      ((∀ i, P.tightAt x i = true → P.A i y = P.b i) ∧ ∀ i, P.Ae i y = P.be i) → y = x := by
    rintro y ⟨hy, hye⟩
    have hd : ∀ i, P.A i x = P.b i → P.A i (y - x) = 0 := by
      intro i hi
      have : P.A i y = P.b i := hy i (by simp only [HPolytope.tightAt, if_pos hi])
      rw [map_sub, this, hi, sub_self]
    have hde : ∀ i, P.Ae i (y - x) = 0 := by
      intro i
      rw [map_sub, hye i, hx.2 i, sub_self]
    have := hpin (y - x) hd hde
    rwa [sub_eq_zero] at this
  -- uniqueness is what makes the `dif_pos` branch name `x` itself
  have hex : ∃! y : Vec ℝ n,
      (∀ i, P.tightAt x i = true → P.A i y = P.b i) ∧ ∀ i, P.Ae i y = P.be i := by
    refine ⟨x, ⟨fun i hi => ?_, hx.2⟩, hspec⟩
    by_cases h : P.A i x = P.b i
    · exact h
    · rw [HPolytope.tightAt, if_neg h] at hi
      exact absurd hi (by simp)
  rw [HPolytope.basicPoint, dif_pos hex]
  exact hspec _ hex.choose_spec.1

end


-- =======================================  MAIN THEOREM  ======================================= --

-- the other way: `aux_contains_of_pinned` asks only that every extreme point be listed
theorem HPolytope.vPolytope_contains (P : HPolytope (Vec ℝ n)) (hc : IsCompact P.construct)
    (hne : P.construct.Nonempty) : -- --- CONCL ---
    P.construct ⊆ (P.vPolytope hne).construct := by -- --- PROOF ---
  refine HPolytope.aux_contains_of_pinned hc _ fun x hx hpin => ?_
  refine ⟨(signEquiv P.m).symm (P.tightAt x), ?_⟩
  show (if P.basicPoint (signEquiv P.m ((signEquiv P.m).symm (P.tightAt x))) ∈ P.construct then
      P.basicPoint (signEquiv P.m ((signEquiv P.m).symm (P.tightAt x))) else hne.choose) = x
  rw [Equiv.apply_symm_apply, P.aux_basicPoint_tightAt hx hpin, if_pos hx]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

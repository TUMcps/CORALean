module

public import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
public import CORALean.ContSet.HPolytope.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Extreme points of a halfspace description

The characterisation vertex enumeration rests on: at an extreme point the rows
that are tight there, together with the equalities, pin the point down
completely. Any direction they all fail to see could be stepped along in both
directions without leaving the polytope — the tight rows stay tight, the slack
ones have room — which puts the point strictly between two others and so is not
extreme.

The step size comes from openness rather than from a minimum over the slack
rows: finitely many strict inequalities cut out an open set, and any small
enough step stays inside it. That avoids having to handle a polytope with no
slack rows at all as a separate case.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.eq_zero_of_extremePoint (P : HPolytope (Vec ℝ n)) {x : Vec ℝ n}
    (hx : x ∈ P.construct.extremePoints ℝ) {d : Vec ℝ n}
    (htight : ∀ i, P.A i x = P.b i → P.A i d = 0) (heq : ∀ i, P.Ae i d = 0) :
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

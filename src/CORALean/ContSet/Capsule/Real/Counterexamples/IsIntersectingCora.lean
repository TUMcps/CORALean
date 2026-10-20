module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.Global.EuclideanNorm
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# CORA's capsule–capsule `isIntersecting_` misses an intersection

`aux_isIntersecting_capsule` of `@capsule/isIntersecting_.m` (l. 103-143) poses the quadratic
programme in `(t₁, t₂)` over `[-1, 1]²` with `H = ½ M`, where the squared axis distance needs
`H = 2 M` in the solvers' `½ xᵀHx + fᵀx`. For `C₁ = capsule([0;0],[1;0],0.1)` and
`C₂ = capsule([0.5;0],[0;1],0.1)` every minimiser has `t₁ = 1`, so `dist ≥ 0.5 > 0.2` and CORA
answers `false`, though `(0.5, 0)` lies in both. The solver `quadprog H f lb ub` is any minimiser of
the objective over the box (`CORAquadprog`). Read from the source, not run.
`Capsule.isIntersecting_` is the sound test.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* two intersecting capsules that CORA's `isIntersecting_` reports as disjoint
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean Matrix

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- `aux_isIntersecting_capsule(C1, C2)` as printed, `CORAquadprog` being `quadprog`. -/
def Capsule.isIntersectingCora
    (quadprog : Mat ℝ 2 2 → Vec ℝ 2 → Vec ℝ 2 → Vec ℝ 2 → Vec ℝ 2) (C₁ C₂ : Capsule n) : Prop :=
  let c1 := C₁.c
  let c2 := C₂.c
  let g1 := C₁.g
  let g2 := C₂.g
  let H : Mat ℝ 2 2 := (1 / 2 : ℝ) • !![g1 ⬝ᵥ g1, -(g1 ⬝ᵥ g2); -(g1 ⬝ᵥ g2), g2 ⬝ᵥ g2]
  let f : Vec ℝ 2 := (2 : ℝ) • ![(c1 - c2) ⬝ᵥ g1, -((c1 - c2) ⬝ᵥ g2)]
  let lb : Vec ℝ 2 := ![-1, -1]
  let ub : Vec ℝ 2 := ![1, 1]
  let x := quadprog H f lb ub
  let p1 := c1 + x 0 • g1
  let p2 := c2 + x 1 • g2
  let dist := ‖p1 - p2‖₂
  let combinedRadius := C₁.r + C₂.r
  let tol : ℝ := 1 / 10 ^ 8
  dist < combinedRadius ∨ |dist - combinedRadius| ≤ tol ∨
    |dist - combinedRadius| ≤ tol * min |dist| |combinedRadius|

end CORALean.Real

namespace CORALean.Real

open CORALean Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.isIntersecting_cora_counterexample : -- --- CONCL ---
    let C₁ : Capsule 2 := ⟨![0, 0], ![1, 0], 1 / 10⟩
    let C₂ : Capsule 2 := ⟨![1 / 2, 0], ![0, 1], 1 / 10⟩
    let IsQuadprog := fun quadprog : Mat ℝ 2 2 → Vec ℝ 2 → Vec ℝ 2 → Vec ℝ 2 → Vec ℝ 2 =>
      ∀ H f lb ub, lb ≤ ub →
        quadprog H f lb ub ∈ Set.Icc lb ub ∧ ∀ y ∈ Set.Icc lb ub,
          1 / 2 * (quadprog H f lb ub ⬝ᵥ H *ᵥ quadprog H f lb ub) + f ⬝ᵥ quadprog H f lb ub ≤
            1 / 2 * (y ⬝ᵥ H *ᵥ y) + f ⬝ᵥ y
    (C₁.construct ∩ C₂.construct).Nonempty ∧ (∃ quadprog, IsQuadprog quadprog) ∧
      ∀ quadprog, IsQuadprog quadprog →
        ¬ Capsule.isIntersectingCora quadprog C₁ C₂ := by -- --- PROOF ---
  intro C₁ C₂ IsQuadprog
  refine ⟨?_, ?_, ?_⟩
  · -- `(0.5, 0)` is the center of `C₂` and the point `t = 0.5` of the axis of `C₁`
    refine ⟨![1 / 2, 0], ⟨1 / 2, by norm_num, ?_⟩, ⟨0, by norm_num, ?_⟩⟩ <;>
      simp [C₁, C₂, Fin.sum_univ_two]
  · -- a continuous objective attains its minimum on a nonempty compact box
    have hex : ∀ (H : Mat ℝ 2 2) (f lb ub : Vec ℝ 2), lb ≤ ub → ∃ x ∈ Set.Icc lb ub,
        IsMinOn (fun y : Vec ℝ 2 => 1 / 2 * (y ⬝ᵥ H *ᵥ y) + f ⬝ᵥ y) (Set.Icc lb ub) x := by
      intro H f lb ub hle
      refine isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hle) ?_
      have hc : Continuous (fun y : Vec ℝ 2 => 1 / 2 * (y ⬝ᵥ H *ᵥ y) + f ⬝ᵥ y) := by
        simp only [dotProduct, mulVec]
        fun_prop
      exact hc.continuousOn
    classical
    refine ⟨fun H f lb ub => if h : lb ≤ ub then (hex H f lb ub h).choose else lb, ?_⟩
    intro H f lb ub hle
    simp only [dif_pos hle]
    exact ⟨(hex H f lb ub hle).choose_spec.1,
      fun y hy => (hex H f lb ub hle).choose_spec.2 hy⟩
  · intro quadprog hqp hcora
    have hle : (![-1, -1] : Vec ℝ 2) ≤ ![1, 1] := by
      intro i; fin_cases i <;> norm_num
    simp only [Capsule.isIntersectingCora] at hcora
    obtain ⟨⟨hlo, hhi⟩, hmin⟩ := hqp _ _ _ _ hle
    set x := quadprog _ _ _ _ with hx
    -- the objective at `x` against the point `(1, x₂)` forces `x₁ = 1`
    have hy : (![1, x 1] : Vec ℝ 2) ∈ Set.Icc (![-1, -1] : Vec ℝ 2) ![1, 1] := by
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp
      · exact hlo 1
      · exact hhi 1
    have h := hmin _ hy
    have h0lo := hlo 0
    have h0hi := hhi 0
    simp [C₁, C₂, dotProduct, mulVec, Fin.sum_univ_two] at h h0lo h0hi
    have hx0 : x 0 = 1 := by nlinarith
    -- so the axis points are `(1, 0)` and `(0.5, x₂)`, at least `0.5` apart
    have hdist : 1 / 2 ≤ ‖(C₁.c + x 0 • C₁.g) - (C₂.c + x 1 • C₂.g)‖₂ := by
      unfold norm₂
      refine Real.le_sqrt_of_sq_le ?_
      simp [C₁, C₂, Fin.sum_univ_two, hx0]
      nlinarith [sq_nonneg (x 1)]
    simp only [C₁, C₂] at hcora hdist
    set d := ‖_‖₂ with hd
    have hmin' : min |d| |1 / 10 + 1 / 10| ≤ 1 / 5 := by
      refine (min_le_right _ _).trans ?_
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10 + 1 / 10)]
      norm_num
    rw [abs_of_pos (by linarith : (0 : ℝ) < d - (1 / 10 + 1 / 10))] at hcora
    rcases hcora with h1 | h1 | h1
    · linarith
    · norm_num at h1; linarith
    · have : (1 / 10 ^ 8 : ℝ) * min |d| |1 / 10 + 1 / 10| ≤ 1 / 10 ^ 8 * (1 / 5) :=
        mul_le_mul_of_nonneg_left hmin' (by norm_num)
      norm_num at h1 this; linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

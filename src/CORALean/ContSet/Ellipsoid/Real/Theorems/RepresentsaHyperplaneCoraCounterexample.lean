import CORALean.ContSet.Ellipsoid.Real.Operations.RepresentsaHyperplaneCora
import CORALean.Global.NotHyperplaneOneDim
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# CORA's `ellipsoid/representsa_(E, 'hyperplane')` accepts every one-dimensional ellipsoid

The branch `'hyperplane'` (l. 143-146) is `res = n == 1`. The ellipsoid
`[-1, 1] = {q + G u | |u| ≤ 1}`
with `q = 0`, `G = (1)` is one-dimensional, so CORA answers `true`, though in one dimension a
hyperplane `{x | a x = b}`, `a ≠ 0`, is a single point and `[-1, 1]` holds `0` and `1`. A wrong
answer, not unsound. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `q = 0`, `G = (1)`: the interval `[-1, 1]`. -/
def Ellipsoid.aux_unitSegment : Ellipsoid 1 := ⟨1, fun _ => 0, fun _ _ => 1⟩

theorem Ellipsoid.aux_zero_mem : (fun _ => (0 : ℝ)) ∈ Ellipsoid.aux_unitSegment.construct := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simp [Ellipsoid.aux_unitSegment, CORALean.norm₂]
  · ext i; simp [Ellipsoid.aux_unitSegment, Matrix.mulVec, dotProduct]

theorem Ellipsoid.aux_one_mem : (fun _ => (1 : ℝ)) ∈ Ellipsoid.aux_unitSegment.construct := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · simp [Ellipsoid.aux_unitSegment, CORALean.norm₂]
  · ext i; simp [Ellipsoid.aux_unitSegment, Matrix.mulVec, dotProduct]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is a segment of positive length, no hyperplane; CORA answers `true`. -/
theorem Ellipsoid.representsa_hyperplane_cora_counterexample :
    (¬ ∃ (f : (Fin 1 → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧
        Ellipsoid.aux_unitSegment.construct = {x | f x = c}) ∧
      Ellipsoid.aux_unitSegment.representsaHyperplaneCora = true := by -- --- PROOF ---
  refine ⟨CORALean.not_hyperplane_of_two_points_fin1 Ellipsoid.aux_zero_mem
    Ellipsoid.aux_one_mem ?_, by simp [Ellipsoid.representsaHyperplaneCora]⟩
  intro h
  have := congrFun h 0
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

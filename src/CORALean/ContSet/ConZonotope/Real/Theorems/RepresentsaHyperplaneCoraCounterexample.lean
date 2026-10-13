import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaHyperplaneCora
import CORALean.Global.NotHyperplaneOneDim
import Mathlib.Tactic.Linarith

/-!
# CORA's `conZonotope/representsa_(cZ, 'hyperplane')` accepts every one-dimensional set

The branch `'hyperplane'` (l. 111-114) is `res = n == 1`. The constrained zonotope with `c = 0`, one
generator `G = (1)` and no constraint is the interval `[-1, 1]` and one-dimensional, so CORA
answers `true`, though in one dimension a hyperplane `{x | a x = b}`, `a ≠ 0`, is a single point
and `[-1, 1]` holds `0` and `1`. A wrong answer, not unsound. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `c = 0`, `G = (1)`, no constraint rows: the interval `[-1, 1]`. -/
def ConZonotope.aux_unitSegment : ConZonotope (Vec ℝ 1) :=
  ⟨1, fun _ => 0, fun _ _ => 1, ⟨0, Fin.elim0, Fin.elim0, 0, Fin.elim0, Fin.elim0⟩⟩

theorem ConZonotope.aux_mem (t : ℝ) (ht : |t| ≤ 1) :
    (fun _ => t) ∈ ConZonotope.aux_unitSegment.construct := by
  refine ⟨fun _ => t, fun _ => ht, ⟨fun i => i.elim0, fun i => i.elim0⟩, ?_⟩
  ext i
  simp [ConZonotope.aux_unitSegment]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is a segment of positive length, no hyperplane; CORA answers `true`. -/
theorem ConZonotope.representsa_hyperplane_cora_counterexample :
    (¬ ∃ (f : (Fin 1 → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧
        ConZonotope.aux_unitSegment.construct = {x | f x = c}) ∧
      ConZonotope.aux_unitSegment.representsaHyperplaneCora = true := by -- --- PROOF ---
  refine ⟨CORALean.not_hyperplane_of_two_points_fin1 (ConZonotope.aux_mem 0 (by norm_num))
    (ConZonotope.aux_mem 1 (by norm_num)) ?_, by simp [ConZonotope.representsaHyperplaneCora]⟩
  intro h
  have := congrFun h 0
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

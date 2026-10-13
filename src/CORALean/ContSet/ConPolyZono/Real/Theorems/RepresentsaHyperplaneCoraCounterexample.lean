module

public import CORALean.ContSet.ConPolyZono.Real.Operations.RepresentsaHyperplaneCora
public import CORALean.Global.NotHyperplaneOneDim
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# CORA's `conPolyZono/representsa_(cPZ, 'hyperplane')` accepts every one-dimensional set

The branch `'hyperplane'` (l. 82-85) is `res = n == 1`. The constrained polynomial zonotope with
`c = 0`, one factor, one dependent generator `G = (1)` with exponent `1` and no constraint is the
interval `[-1, 1]` and one-dimensional, so CORA answers `true`, though in one dimension a
hyperplane `{x | a x = b}`, `a ≠ 0`, is a single point and `[-1, 1]` holds `0` and `1`. A wrong
answer, not unsound. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `c = 0`, `G = (1)`, `E = (1)`, no constraint: the interval `[-1, 1]`. -/
def ConPolyZono.aux_unitSegment : ConPolyZono (Vec ℝ 1) :=
  ⟨1, 1, 0, 0, 0, fun _ => 0, fun _ _ => 1, fun _ _ => 1, Fin.elim0, fun i => i.elim0,
    ⟨fun i => i.elim0, fun i => i.elim0⟩, fun _ j => j.elim0⟩

theorem ConPolyZono.aux_mem (t : ℝ) (ht : |t| ≤ 1) :
    (fun _ => t) ∈ ConPolyZono.aux_unitSegment.construct := by
  refine ⟨fun _ => t, Fin.elim0, fun _ => ht, fun j => j.elim0, fun i => i.elim0, ?_⟩
  ext i
  simp [ConPolyZono.aux_unitSegment, PolyZonotope.monomial]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is a segment of positive length, no hyperplane; CORA answers `true`. -/
theorem ConPolyZono.representsa_hyperplane_cora_counterexample :
    (¬ ∃ (f : (Fin 1 → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧
        ConPolyZono.aux_unitSegment.construct = {x | f x = c}) ∧
      ConPolyZono.aux_unitSegment.representsaHyperplaneCora = true := by -- --- PROOF ---
  refine ⟨CORALean.not_hyperplane_of_two_points_fin1 (ConPolyZono.aux_mem 0 (by norm_num))
    (ConPolyZono.aux_mem 1 (by norm_num)) ?_, by simp [ConPolyZono.representsaHyperplaneCora]⟩
  intro h
  have := congrFun h 0
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.Global.NotHyperplaneOneDim
public import Mathlib.Tactic.Linarith
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `ConPolyZono.representsaHyperplaneCora`: the `'hyperplane'` test as CORA's code computes it

`@conPolyZono/representsa_.m` opens with `representsa_emptyObject` (a set without data, of dimension
zero here, is answered first) and then reads, for `type = 'hyperplane'` (l. 82-85),

```
% constrained polynomial zonotopes cannot be unbounded (unless 1D, where hyperplane is also bounded)
res = n == 1;
```

so every one-dimensional set is answered `true`. In one dimension a hyperplane `{x | a x = b}`,
`a ≠ 0`, is a single point; a set of positive length is not. Read from the source, not run.

# CORA's `conPolyZono/representsa_(cPZ, 'hyperplane')` accepts every one-dimensional set

The branch `'hyperplane'` (l. 82-85) is `res = n == 1`. The constrained polynomial zonotope with
`c = 0`, one factor, one dependent generator `G = (1)` with exponent `1` and no constraint is the
interval `[-1, 1]` and one-dimensional, so CORA answers `true`, though in one dimension a
hyperplane `{x | a x = b}`, `a ≠ 0`, is a single point and `[-1, 1]` holds `0` and `1`. A wrong
answer, not unsound. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA answers hyperplane for a segment
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `res` for `representsa_(conPolyZono, 'hyperplane')`, nonempty object, dimension `n`. -/
def ConPolyZono.representsaHyperplaneCora (_cPZ : ConPolyZono (Vec ℝ n)) : Bool :=
  -- n = dim(conPolyZono)
  let dim := n
  -- res = n == 1
  dim == 1

end CORALean.Real

namespace CORALean.Real


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `c = 0`, `G = (1)`, `E = (1)`, no constraint: the interval `[-1, 1]`. -/
@[step_of ConPolyZono.representsa_hyperplane_cora_counterexample]
def ConPolyZono.step_unitSegment : ConPolyZono (Vec ℝ 1) :=
  ⟨1, 1, 0, fun _ => 0, fun _ _ => 1, fun _ _ => 1, Fin.elim0, ⟨0, 0, fun i => i.elim0,
      fun _ j => j.elim0, fun i => i.elim0, fun _ => .eq, Interval.unit 1⟩,
      fun _ => rfl, rfl⟩


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem ConPolyZono.aux_mem (t : ℝ) (ht : |t| ≤ 1) :
    (fun _ => t) ∈ ConPolyZono.step_unitSegment.construct := by
  refine ⟨fun _ => t, Fin.elim0, fun j => j.elim0,
    ⟨(Interval.mem_unit_iff _).mpr fun _ => ht, fun i => i.elim0⟩, ?_⟩
  ext i
  simp [ConPolyZono.step_unitSegment, PolyZonotope.monomial]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is a segment of positive length, no hyperplane; CORA answers `true`. -/
theorem ConPolyZono.representsa_hyperplane_cora_counterexample : -- --- CONCL ---
    (¬ ∃ (f : (Fin 1 → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧
        ConPolyZono.step_unitSegment.construct = {x | f x = c}) ∧
      ConPolyZono.step_unitSegment.representsaHyperplaneCora = true := by -- --- PROOF ---
  refine ⟨CORALean.not_hyperplane_of_two_points_fin1 (ConPolyZono.aux_mem 0 (by norm_num))
    (ConPolyZono.aux_mem 1 (by norm_num)) ?_, by simp [ConPolyZono.representsaHyperplaneCora]⟩
  intro h
  have := congrFun h 0
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

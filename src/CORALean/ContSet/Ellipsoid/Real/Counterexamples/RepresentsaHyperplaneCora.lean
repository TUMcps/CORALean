module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstructIff
public import CORALean.Global.NotHyperplaneOneDim
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Ellipsoid.representsaHyperplaneCora`: the `'hyperplane'` test as CORA's code computes it

`@ellipsoid/representsa_.m` opens with `representsa_emptyObject` (a set without data, of dimension
zero here, is answered first) and then reads, for `type = 'hyperplane'` (l. 143-146),

```
% ellipsoid cannot be unbounded (unless 1D, where hyperplane also bounded)
res = n == 1;
```

so every one-dimensional set is answered `true`. In one dimension a hyperplane `{x | a x = b}`,
`a ≠ 0`, is a single point; a set of positive length is not. Read from the source, not run.

# CORA's `ellipsoid/representsa_(E, 'hyperplane')` accepts every one-dimensional ellipsoid

The branch `'hyperplane'` (l. 143-146) is `res = n == 1`. The ellipsoid
`[-1, 1] = {q + G u | |u| ≤ 1}`
with `q = 0`, `Q = (1)` is one-dimensional, so CORA answers `true`, though in one dimension a
hyperplane `{x | a x = b}`, `a ≠ 0`, is a single point and `[-1, 1]` holds `0` and `1`. A wrong
answer, not unsound. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA answers `true` for a segment that is no hyperplane
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `res` for `representsa_(ellipsoid, 'hyperplane')`, nonempty object, dimension `n`. -/
def Ellipsoid.representsaHyperplaneCora (_E : Ellipsoid n) : Bool :=
  -- n = dim(ellipsoid)
  let dim := n
  -- res = n == 1
  dim == 1

end CORALean.Real

namespace CORALean.Real

open Matrix
open scoped MatrixOrder


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `q = 0`, `Q = (1)`: the interval `[-1, 1]`. -/
def Ellipsoid.aux_unitSegment : Ellipsoid 1 := ⟨1, fun _ => 0, .one⟩

/-- Its generator is `(1)`. -/
theorem Ellipsoid.aux_unitSegment_G : Ellipsoid.aux_unitSegment.G = 1 := CFC.sqrt_one

theorem Ellipsoid.aux_zero_mem : (fun _ => (0 : ℝ)) ∈ Ellipsoid.aux_unitSegment.construct := by
  refine Ellipsoid.mem_construct_iff.2 ⟨fun _ => 0, ?_, ?_⟩
  · simp [CORALean.norm₂]
  · rw [Ellipsoid.aux_unitSegment_G, Matrix.one_mulVec]
    ext i; simp [Ellipsoid.aux_unitSegment]

theorem Ellipsoid.aux_one_mem : (fun _ => (1 : ℝ)) ∈ Ellipsoid.aux_unitSegment.construct := by
  refine Ellipsoid.mem_construct_iff.2 ⟨fun _ => 1, ?_, ?_⟩
  · simp [CORALean.norm₂]
  · rw [Ellipsoid.aux_unitSegment_G, Matrix.one_mulVec]
    ext i; simp [Ellipsoid.aux_unitSegment]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is a segment of positive length, no hyperplane; CORA answers `true`. -/
theorem Ellipsoid.representsa_hyperplane_cora_counterexample : -- --- CONCL ---
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

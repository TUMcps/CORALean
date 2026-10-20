module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.Global.NotHyperplaneOneDim
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `ConZonotope.representsaHyperplaneCora`: the `'hyperplane'` test as CORA's code computes it

`@conZonotope/representsa_.m` opens with `representsa_emptyObject` (a set without data, of dimension
zero here, is answered first) and then reads, for `type = 'hyperplane'` (l. 111-114),

```
% constrained zonotopes cannot be unbounded (unless 1D, where hyperplane is also bounded)
res = n == 1;
```

so every one-dimensional set is answered `true`. In one dimension a hyperplane `{x | a x = b}`,
`a ≠ 0`, is a single point; a set of positive length is not. Read from the source, not run.

# CORA's `conZonotope/representsa_(cZ, 'hyperplane')` accepts every one-dimensional set

The branch `'hyperplane'` (l. 111-114) is `res = n == 1`. The constrained zonotope with `c = 0`, one
generator `G = (1)` and no constraint is the interval `[-1, 1]` and one-dimensional, so CORA
answers `true`, though in one dimension a hyperplane `{x | a x = b}`, `a ≠ 0`, is a single point
and `[-1, 1]` holds `0` and `1`. A wrong answer, not unsound. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's hyperplane test accepts a segment that is no hyperplane
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `res` for `representsa_(conZonotope, 'hyperplane')`, nonempty object, dimension `n`. -/
def ConZonotope.representsaHyperplaneCora (_cZ : ConZonotope (Vec ℝ n)) : Bool :=
  -- n = dim(conZonotope)
  let dim := n
  -- res = n == 1
  dim == 1

end CORALean.Real

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

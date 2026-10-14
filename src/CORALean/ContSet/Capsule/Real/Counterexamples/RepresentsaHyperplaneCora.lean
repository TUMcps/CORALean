module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.Global.NotHyperplaneOneDim
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Capsule.representsaHyperplaneCora`: the `'hyperplane'` test as CORA's code computes it

`@capsule/representsa_.m` opens with `representsa_emptyObject` (a set without data, of dimension
zero here, is answered first) and then reads, for `type = 'hyperplane'` (l. 143-146),

```
% capsule cannot be unbounded (except 1D where hyperplane also bounded)
res = n == 1;
```

so every one-dimensional set is answered `true`. In one dimension a hyperplane `{x | a x = b}`,
`a ≠ 0`, is a single point; a set of positive length is not. Read from the source, not run.

# CORA's `capsule/representsa_(C, 'hyperplane')` accepts every one-dimensional capsule

The branch `'hyperplane'` (l. 143-146) is `res = n == 1`. The capsule with `c = 0`, `g = 0`,
`r = 1` is the interval `[-1, 1]` and one-dimensional, so CORA answers `true`, though in one
dimension a hyperplane `{x | a x = b}`, `a ≠ 0`, is a single point and `[-1, 1]` holds `0` and `1`.
A wrong answer, not unsound. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `res` for `representsa_(capsule, 'hyperplane')`, nonempty object, dimension `n`. -/
def Capsule.representsaHyperplaneCora (_C : Capsule n) : Bool :=
  -- n = dim(capsule)
  let dim := n
  -- res = n == 1
  dim == 1

end CORALean.Real

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `c = 0`, `g = 0`, `r = 1`: the interval `[-1, 1]`. -/
def Capsule.aux_unitSegment : Capsule 1 := ⟨fun _ => 0, fun _ => 0, 1⟩

theorem Capsule.aux_zero_mem : (fun _ => (0 : ℝ)) ∈ Capsule.aux_unitSegment.construct :=
  ⟨0, by norm_num, by simp [Capsule.aux_unitSegment]⟩

theorem Capsule.aux_one_mem : (fun _ => (1 : ℝ)) ∈ Capsule.aux_unitSegment.construct :=
  ⟨0, by norm_num, by simp [Capsule.aux_unitSegment]⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is a segment of positive length, no hyperplane; CORA answers `true`. -/
theorem Capsule.representsa_hyperplane_cora_counterexample :
    (¬ ∃ (f : (Fin 1 → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧
        Capsule.aux_unitSegment.construct = {x | f x = c}) ∧
      Capsule.aux_unitSegment.representsaHyperplaneCora = true := by -- --- PROOF ---
  refine ⟨CORALean.not_hyperplane_of_two_points_fin1 Capsule.aux_zero_mem
    Capsule.aux_one_mem ?_, by simp [Capsule.representsaHyperplaneCora]⟩
  intro h
  have := congrFun h 0
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

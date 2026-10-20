module

public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
# `NonlinearSysDT.reachSpecCora`

The verdict `res` of CORA's `@nonlinearSysDT/reach.m` called with an unsafe-set specification,
for `ℝ¹`. `R i` stands for the time-point set `timePoint.set{i+1}` (the sets the algorithm
computes: `outputSet` of `params.X₀` at l. 64 for `i = 0`, of `linReach`'s result at l. 80 for
`i ≥ 1`). The loop `for i = 1:steps` (l. 69) checks only `timePoint.set{i+1}` (l. 87), so the
initial output set `timePoint.set{1}` is never checked.

# CORA's `nonlinearSysDT/reach` never checks the initial set against the specification

`x⁺ = x + 1` from `R0 = {0}` for one step, against the unsafe set `[-1/2, 1/2]`: the initial
state `0` is unsafe, yet `res = true` (the later sets `{1}` are safe). No other code checks
`R0` first: `reach` is the entry point and `check` is called only at l. 87.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the check reports safe although the initial state is unsafe
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- `res`: every checked time-point set is disjoint from the unsafe set. -/
def NonlinearSysDT.reachSpecCora (R : ℕ → Set ℝ) (F : Set ℝ) (steps : ℕ) : Prop :=
  let timePointSet : ℕ → Set ℝ := fun j => R (j - 1)               -- 64, 80. timePoint.set{j}
  ∀ i ∈ Finset.Icc 1 steps, Disjoint (timePointSet (i + 1)) F  -- 69, 87. check(spec,set{i+1})


-- =======================================  MAIN THEOREM  ======================================= --

/-- `res = true`, although the initial state `0` is in the unsafe set. -/
theorem NonlinearSysDT.reachSpecCora_initial_counterexample :
    NonlinearSysDT.reachSpecCora (fun i => (fun x : ℝ => x + 1)^[i] '' {0})
        (Set.Icc (-1 / 2) (1 / 2)) 1 ∧
      (0 : ℝ) ∈ ({0} : Set ℝ) ∩ Set.Icc (-1 / 2) (1 / 2) := by -- --- PROOF ---
  refine ⟨?_, rfl, by constructor <;> norm_num⟩
  intro i hi
  have : i = 1 := by simpa using hi
  subst this
  simp only [Nat.add_sub_cancel, Function.iterate_one, Set.image_singleton, zero_add]
  rw [Set.disjoint_singleton_left]
  rintro ⟨-, h⟩
  norm_num at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

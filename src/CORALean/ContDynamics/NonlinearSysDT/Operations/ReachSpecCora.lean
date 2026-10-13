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
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `res`: every checked time-point set is disjoint from the unsafe set. -/
def NonlinearSysDT.reachSpecCora (R : ℕ → Set ℝ) (F : Set ℝ) (steps : ℕ) : Prop :=
  let timePointSet : ℕ → Set ℝ := fun j => R (j - 1)               -- 64, 80. timePoint.set{j}
  ∀ i ∈ Finset.Icc 1 steps, Disjoint (timePointSet (i + 1)) F  -- 69, 87. check(spec,set{i+1})

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachParams
import CORALean.ContDynamics.NonlinearSysDT.Definitions.WithSteps
import CORALean.ContDynamics.NonlinearSysDT.Operations.Reach
import CORALean.ContSet.SetUnion.SetUnion

/-!
# The steps of the loop as one union, or a run-time failure

`reach` at steps `0` through `K`, one member of the `SetUnion` per step — the
`Reach.reach` field of the instance. Step `k`'s certificate is conservative only
while the state stays in `(steps k).R`, so, as CORA does, the set step `k`
starts from is tested against that step's region before the step is trusted:
`Contains` on `region k`, which runs. One failed test and the answer is `none`,
since nothing after it is sound; `List.all` stops at the first `false`.

The last set, step `K`'s, is tested against nothing: no step starts from it.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S] [∀ n, Contains (Rg n) (S n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Steps `0` through `p.K` of `sys.sys.reach`, or `none` once the set some step
`k < p.K` starts from is not shown inside `sys.region k`. -/
def NonlinearSysDT.WithSteps.reachUnion (sys : NonlinearSysDT.WithSteps S Rg m n)
    (p : NonlinearSysDT.ReachParams) (X₀ : S n) : Option (SetUnion (S n)) :=
  let R := sys.sys.reach p.o p.ho sys.steps X₀                        -- R(k), k = 0, 1, …
  let confined := (List.range p.K).all fun k =>                       -- R(k) ⊆ region k, k < K
    Contains.contains (sys.region k) (R k)
  if confined then some ⟨(List.range (p.K + 1)).map R⟩ else none     -- ⋃_{k ≤ K} R(k), or fail

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

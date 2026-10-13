module

public import CORALean.ContDynamics.NonlinearSysDT.Definitions.WithSteps
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Reach
public import CORALean.ContDynamics.Reach.Definitions.Params
public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# The steps of the loop as one union, or a run-time failure

`reach` at steps `0` through `K = tFinal - tStart`, one member of the `SetUnion` per step — the
`Reach.reach` field of the instance. Step `k`'s certificate is conservative only
while the state stays in `(steps k).R`, so, as CORA does, the set step `k`
starts from is tested against that step's region before the step is trusted:
`Contains` on `region k`, which runs. One failed test and the answer is `none`,
since nothing after it is sound; `List.all` stops at the first `false`.

The last set, step `K`'s, is tested against nothing: no step starts from it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋] [∀ n, Contains (Rg n) (S n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Steps `0` through `K = tFinal - tStart` of `sys.sys.reach`, or `none` once the set
some step `k < K` starts from is not shown inside `sys.region k`. -/
def NonlinearSysDT.WithSteps.reachUnion (sys : NonlinearSysDT.WithSteps S Rg 𝕋 m n)
    (params : Reach.Params (S n) ℕ) (options : NonlinearSysDT.ReachOptions) :
    Option (SetUnion (S n)) :=
  let R₀ := params.X₀                                                 -- the paper's symbols
  let K := params.tFinal - params.tStart                             -- steps
  let R := fun k => sys.sys.reach ⟨R₀, sys.U, 0, k⟩ options sys.steps -- R(k), k = 0, 1, …
  let confined := (List.range K).all fun k =>                         -- R(k) ⊆ region k, k < K
    Contains.contains (sys.region k) (R k)
  if confined then some ⟨(List.range (K + 1)).map R⟩ else none       -- ⋃_{k ≤ K} R(k), or fail

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

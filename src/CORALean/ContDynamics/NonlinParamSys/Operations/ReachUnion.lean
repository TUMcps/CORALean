import CORALean.ContDynamics.NonlinParamSys.Definitions.WithSteps
import CORALean.ContDynamics.NonlinearSys.Operations.ReachUnion
import CORALean.Global.Block

/-!
# The augmented re-linearization loop, projected back, or a run-time failure

The reduction route: `X₀ × P` is the augmented initial set, taken inside one
`Vec` as `Block.lean` takes a product, the images of `X₀` and `P` under the two
padding matrices summed; `NonlinearSys.WithSteps.reachUnion` runs the augmented
system from it; every member of the union it returns is mapped back to the
first `n` coordinates by the selection matrix. `none` is exactly the augmented
run's: some step's start, inflated by `2MΔt`, not shown inside its region in
dimension `n + q` — the parameter's coordinates tested with the state's.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m q n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aug.reachUnion` from `R0 × P` over the same horizon and options, each member
projected to the first `n` coordinates, or `none` where the augmented run fails. -/
noncomputable def NonlinParamSys.WithSteps.reachUnion (sys : NonlinParamSys.WithSteps S Rg m q n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachOptions ℝ) :
    Option (SetUnion (S n)) :=
  let X₀ := params.R0                                                -- the paper's symbols
  let E := LinearMap.toMatrix' (blockPadLeft n q)                    -- x ↦ (x, 0)
  let F := LinearMap.toMatrix' (blockPadRight n q)                   -- p ↦ (0, p)
  let Pr := LinearMap.toMatrix' (blockLeft n q)                      -- (x, p) ↦ x
  let Z₀ := Mtimes.mtimes (𝕄 := Mat ℝ) E X₀ ⊞ Mtimes.mtimes (𝕄 := Mat ℝ) F sys.P  -- X₀ × P
  (sys.aug.reachUnion ⟨Z₀, params.tStart, params.tFinal⟩ options).map fun R =>  -- augmented,
    ⟨R.sets.map (Mtimes.mtimes (𝕄 := Mat ℝ) Pr)⟩                     --   projected back

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

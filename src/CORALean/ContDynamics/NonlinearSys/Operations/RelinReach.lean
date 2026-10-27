module

public import CORALean.ContDynamics.LinearSys.Operations.Discretize
public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinStep
public import CORALean.ContDynamics.NonlinearSys.Definitions.RelinReachOptions
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
public import CORALean.ContDynamics.Reach.Definitions.Params

@[expose] public section

/-!
# The re-linearization loop

CORA's `nonlinearSys/reach`, and the while loop of [1, Alg. 1] — its line 17 `post` and line 18
`reduce`: one linearization per time step, the enclosure reached at the end of a step becoming
the initial set of the next. Nothing new is computed: what re-linearizing costs is a fresh
certificate per step, data the caller supplies. Time is counted in steps, `tStart` and `tFinal`
being ℕ as in `LinearSysDT.reach`, so the sample times are the step boundaries and absolute time
is `iΔt`. `steps` and `Ud` are the certificates CORA computes inside `reach`. `exp` takes the
`l∞` operator norm on `Mat`, a choice.

## Inputs
* `sys` – system
* `U` – input set
* `params` – reachability parameters
* `options` – reachability options
* `steps` – linearization steps
* `Ud` – input enclosures per step

## Output
* the reachable set after the last step

## References

* [1] [N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set Representation for
      Reachability Analysis". IEEE Transactions on Automatic Control,
      2021.](../../../../../references/2021/kochdumper-tac-sparse-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set after `params.tFinal - params.tStart` re-linearized steps of
length `options.Δt`, from `params.X₀` under the per-step input enclosures
`Ud`, held at maximum order `options.ρ`. -/
noncomputable def NonlinearSys.relinReach (sys : NonlinearSys n m) {U : S m}
    (params : Reach.Params (S n) ℕ) (options : NonlinearSys.RelinReachOptions)
    (steps : ℕ → sys.LinStep U) (Ud : ℕ → S n) : S n :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let o := options.ρ
  let N := params.tFinal - params.tStart                           -- steps
  let step := fun i R => ((NonlinearSys.linearize (steps i).A).discretize Δt).reach
    ⟨R, Ud i, 0, 1⟩ ⟨o, options.hZonotopeOrder⟩                    -- one linearization, one step
  Nat.rec (motive := fun _ => S n) R₀ step N                        -- R(NΔt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

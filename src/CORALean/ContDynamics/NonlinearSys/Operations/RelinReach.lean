import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContDynamics.NonlinearSys.Definitions.LinStep
import CORALean.ContDynamics.NonlinearSys.Definitions.RelinReachOptions
import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
import CORALean.ContDynamics.Reach.Definitions.Params

/-!
# The re-linearization loop

CORA's `nonlinearSys/reach`, and the while loop of [1, Alg. 1] — its line 17
`post` and its line 18 `reduce`: one linearization per time step, the enclosure
reached at the end of a step becoming the initial set of the next. Step `i` runs
the linear machinery of step `i`'s own system for exactly one step, so the whole
loop is one step of `LinearSysDT.reach` iterated at a matrix that changes each time.

Nothing new is computed: what re-linearizing costs is a fresh certificate per step,
data the caller supplies. One step per linearization, so the sample times are the
step boundaries and absolute time is `iΔt`.

Time is counted in steps, `tStart` and `tFinal` being ℕ as in `LinearSysDT.reach`,
not in ℚ with `Reach.steps`: `timeStep` is an ℝ that `discretize` needs, and the
guarantees are stated at every boundary `iΔt`, which in ℚ time would be a partial
`Option` per horizon. The count `tFinal - tStart` is exact, and every guarantee is
stated at `tStart = 0`. `steps` and `Ud` are the certificates CORA computes inside
`reach`. `exp` takes the `l∞` operator norm on `Mat`, a choice.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


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
length `options.timeStep`, from `params.R0` under the per-step input enclosures
`Ud`, held at maximum order `options.zonotopeOrder`. -/
noncomputable def NonlinearSys.relinReach (sys : NonlinearSys n m) {U : S m}
    (params : Reach.Params (S n) ℕ) (options : NonlinearSys.RelinReachOptions)
    (steps : ℕ → sys.LinStep U) (Ud : ℕ → S n) : S n :=
  let R₀ := params.R0                                               -- the paper's symbols
  let Δt := options.timeStep
  let o := options.zonotopeOrder
  let N := params.tFinal - params.tStart                           -- steps
  let step := fun i R => ((NonlinearSys.linearize (steps i).A).discretize Δt).reach
    ⟨R, Ud i, 0, 1⟩ ⟨o, options.hZonotopeOrder⟩                    -- one linearization, one step
  Nat.rec (motive := fun _ => S n) R₀ step N                        -- R(NΔt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

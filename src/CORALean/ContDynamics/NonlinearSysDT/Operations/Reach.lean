import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachOptions
import CORALean.ContDynamics.NonlinearSysDT.Operations.LinInput
import CORALean.ContDynamics.NonlinearSysDT.Operations.Linearize
import CORALean.ContDynamics.Reach.Definitions.InputParams

/-!
# Reachability of a discrete nonlinear system

CORA's `nonlinearSysDT/reach`, one linearization per step: step `k` runs
`LinearSysDT.reach` for one step at `(steps k).A`, on the widened input `(steps k)
.linInput`, the set reached at the end of a step becoming the initial set of
the next. Unlike `NonlinearSys.relinReach` there is no `discretize` and no
`Δt`: the matrix a step's certificate is issued for is already the discrete
system's own, so nothing converts it.

Time is counted in sampling periods (`ℕ`), as in `LinearSysDT.reach`, and step `i`
is the `i`-th after `tStart`. `steps` stays positional, unlike CORA, which
computes the linearizations inside `reach`: here they are certificates a caller
supplies.

`params.U` is the input set the linearizations `steps` are issued for; the
discrete step itself needs no more than `linInput`, the discrete analogue of
`NonlinearSys.reach_outer_inputSolution`, folded into the definition.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set at time `tFinal`, from `R₀` at `tStart` under the per-step
linearizations `steps`, held at maximum order `zonotopeOrder`. -/
def NonlinearSysDT.reach (sys : NonlinearSysDT n m) (params : Reach.InputParams (S n) (S m) ℕ)
    (options : NonlinearSysDT.ReachOptions) (steps : ℕ → sys.LinStep params.U) : S n :=
  let R₀ := params.R0                                               -- the paper's symbols
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let step := fun (i : ℕ) (R : S n) => (NonlinearSysDT.linearize (steps i).A).reach
    ⟨R, (steps i).linInput, 0, 1⟩ ⟨options.zonotopeOrder, options.hZonotopeOrder⟩
  Nat.fold N (fun i _ R => step i R) R₀                            -- R_N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

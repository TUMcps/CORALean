module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachOptions
public import CORALean.ContDynamics.NonlinearSysDT.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Linearize
public import CORALean.ContDynamics.Reach.Definitions.InputParams

@[expose] public section

/-!
# Reachability of a discrete nonlinear system

CORA's `nonlinearSysDT/reach`, one linearization per step: step `k` runs `LinearSysDT.reach` for
one step at `(steps k).A`, on the widened input `(steps k).linInput`, the set reached at the end
of a step becoming the initial set of the next. Unlike `NonlinearSys.relinReach` there is no
`discretize` and no `Δt`: the matrix a step's certificate is issued for is already the discrete
system's own. Time is counted in sampling periods (`ℕ`), as in `LinearSysDT.reach`. `steps`
stays positional, unlike CORA, which computes the linearizations inside `reach`: here they are
certificates a caller supplies, and `params.U` is the input set they are issued for.

## Inputs
* `sys` – system
* `params` – reachability parameters
* `options` – reachability options
* `steps` – linearization steps

## Output
* the reachable set at the final time
-/

-- Authors:       Claude Sonnet 5
-- Written:       04-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set at time `tFinal`, from `R₀` at `tStart` under the per-step
linearizations `steps`, held at maximum order `ρ`. -/
def NonlinearSysDT.reach (sys : NonlinearSysDT n m) (params : Reach.InputParams (S n) (S m) ℕ)
    (options : NonlinearSysDT.ReachOptions) (steps : ℕ → sys.LinStep 𝕋 params.U) : S n :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let step := fun (i : ℕ) (R : S n) => (NonlinearSysDT.linearize (steps i).A).reach
    ⟨R, (steps i).linInput, 0, 1⟩ ⟨options.ρ, options.hZonotopeOrder⟩
  Nat.fold N (fun i _ R => step i R) R₀                            -- R_N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

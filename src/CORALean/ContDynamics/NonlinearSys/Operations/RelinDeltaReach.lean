module

public import CORALean.ContDynamics.LinearSys.Operations.DeltaReach
public import CORALean.ContDynamics.NonlinearSys.Definitions.RelinDeltaReachOptions
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinReach

@[expose] public section

/-!
# The state differences step `i` of the loop spans

`relinTimeInterval` says where step `i` *is*; this says how far it has *moved* from where it
started: `LinearSys.deltaReach` of the linearized system at `(steps i).A`, applied to what
`relinReach` reaches at the step's start, plus step `i`'s own input enclosure — the shape
`IsCanonicalTrajectory.deltaReach_outer` proves. CORA's `Rdiff`, computed once per step by
`linReach` before the abstraction error is estimated: `priv_abstrerr_poly` splits the second-order
term at `x = z + δ`, and each product left over carries at least one `δ`.

## Inputs
* `sys` – system
* `U` – input set
* `params` – reachability parameters
* `options` – reachability options
* `steps` – linearization steps
* `Ud` – input enclosures per step

## Output
* the differences step `i` spans
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every difference between a state of step `i = params.tFinal - params.tStart` and
the state that step started from, from what `relinReach` reaches at `iΔt` and step
`i`'s input enclosure. Time is counted in steps, as in `relinReach`. -/
noncomputable def NonlinearSys.relinDeltaReach (sys : NonlinearSys n m) {U : S m}
    (params : Reach.Params (S n) ℕ) (options : NonlinearSys.RelinDeltaReachOptions)
    (steps : ℕ → sys.LinStep U) (Ud : ℕ → S n) : S n :=
  let Δt := options.Δt                                       -- the paper's symbols
  let η := options.η
  let i := params.tFinal - params.tStart                           -- the step
  let R := sys.relinReach params options.toRelinReachOptions steps Ud  -- R(iΔt)
  ((NonlinearSys.linearize (steps i).A).deltaReach Δt η R) ⊞ Ud i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

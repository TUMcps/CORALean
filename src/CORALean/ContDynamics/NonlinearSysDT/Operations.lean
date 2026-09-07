import CORALean.ContDynamics.LinearSysDT.Operations
import CORALean.ContDynamics.NonlinearSysDT.LinStep

/-!
# Reachability of a discrete nonlinear system

CORA's `nonlinearSysDT/reach`, one linearization per step: step `k` runs
`LinearSysDT.reach ... 1` at `(steps k).A`, on the widened input `(steps k)
.linInput`, the set reached at the end of a step becoming the initial set of
the next. Unlike `NonlinearSys.relinReach` there is no `discretize` and no
`Δt`: the matrix a step's certificate is issued for is already the discrete
system's own, so nothing converts it.

`Ud` is not a parameter, unlike `LinearSysDT.reach`'s `U`: the discrete step
needs no more than `linInput`, so there is nothing for a caller to name beyond
the linearization itself — the discrete analogue of `NonlinearSys
.reach_outer_inputSolution`, folded into the definition rather than proved
separately, since here the "solution" is one evaluation, not an integral.

`simulate` samples one run directly against `sys.f`, no linearization needed:
a point computation carrying none of `reach`'s set instances.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- The linear system a linearization at any matrix `A` leaves behind. Fresh
rather than `NonlinearSys.linearize`, whose target `LinearSys` carries a flow
this system has none of. -/
def NonlinearSysDT.linearize (A : Mat ℝ n n) : LinearSysDT ℝ n := ⟨A⟩

variable {m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set after `k` re-linearized steps, from `R₀` under the
per-step linearizations `steps`, held at maximum order `o`. `ho` is what rules
out `o = 0`. -/
def NonlinearSysDT.reach (sys : NonlinearSysDT n m) {U : S m} (o : ℕ) (ho : 0 < o)
    (steps : ℕ → sys.LinStep U) (R₀ : S n) : ℕ → S n
  | 0 => R₀
  | k + 1 => (NonlinearSysDT.linearize (steps k).A).reach o ho
      (sys.reach o ho steps R₀ k) (steps k).linInput 1

omit [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
    [Mtimes (Mat ℝ) S] [OfInterval S] in
/-- One sampled run of the dynamics from `x₀` under input signal `u` — a point
computation, none of `reach`'s set instances needed. -/
def NonlinearSysDT.simulate (sys : NonlinearSysDT n m) (x₀ : Vec ℝ n) (u : ℕ → Vec ℝ m) :
    ℕ → Vec ℝ n
  | 0 => x₀
  | k + 1 => sys.f (sys.simulate x₀ u k) (u k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

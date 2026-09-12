import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSysDT.Operations
import CORALean.ContDynamics.NonlinearSys.LinStep
import CORALean.ContDynamics.NonlinearSys.Operations.Linearize

/-!
# The re-linearization loop

CORA's `nonlinearSys/reach`, and the while loop of [1, Alg. 1] — its line 17
`post` and its line 18 `reduce`: one linearization per time step, the enclosure
reached at the end of a step becoming the initial set of the next. Step `i` runs
the linear machinery of step `i`'s own system for exactly one step, so the whole
loop is `LinearSysDT.reach ... 1` iterated at a matrix that changes each time.

Nothing new is computed. `linearize` gives the system, `discretize` samples it and
`reach` takes the step; what re-linearizing costs is a fresh certificate per step,
which is data the caller supplies.

One step per linearization rather than a horizon per linearization, so the sample
times are the step boundaries and absolute time is `iΔt`. `Δt` and `o` are
uniform, so `relinReach` recurses on the step index alone.

`exp` needs a norm on `Mat` — a choice, not an instance — and it is the `l∞`
operator norm here as everywhere `discretize` is reasoned about.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   13-September-2026
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

/-- The reachable set after `i` re-linearized steps of length `Δt`, from `R₀`
under the per-step input enclosures `Ud`, held at maximum order `o`. `ho` is
what rules out `o = 0`. -/
noncomputable def NonlinearSys.relinReach (sys : NonlinearSys n m) {U : S m} (o : ℕ) (ho : 0 < o)
    (Δt : ℝ) (steps : ℕ → sys.LinStep U) (Ud : ℕ → S n) (R₀ : S n) : ℕ → S n
  | 0 => R₀
  | i + 1 => ((NonlinearSys.linearize (steps i).A).discretize Δt).reach o ho
      (sys.relinReach o ho Δt steps Ud R₀ i) (Ud i) 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

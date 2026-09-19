import CORALean.ContDynamics.LinearSys.PerturbedTrajectory

/-!
# The states no admissible input can keep out of the target

[1, Def. 6]: the time-point minimal backward reachable set `R^{∀∃}(-t)`. A
state `x₀` is in it when, whatever admissible input signal is applied, some
admissible disturbance signal still drives the perturbed run into `Xend` at
time `t` — the states the target is unavoidable from.

`∀u` guards which `u` the outer quantifier ranges over; `PerturbedTrajectory`
also restates `u`'s own admissibility, which the guard has already made true,
so nothing is lost by carrying it — the same bundle serves the `∃w` half.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state that cannot avoid `Xend` at time `t`: for every admissible
input there is some admissible disturbance whose run lands there. -/
def LinearSys.backReachSetForallExists (sys : LinearSys 𝕋 n) (T : Set ℝ) (U W Xend : S n)
    (t : ℝ) : Set (Vec ℝ n) :=
  {x₀ | ∀ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) →
      ∃ w x : ℝ → Vec ℝ n, sys.PerturbedTrajectory T U W x u w ∧
        x 0 = x₀ ∧ x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

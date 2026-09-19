import CORALean.ContDynamics.LinearSys.PerturbedTrajectory

/-!
# The states one admissible input can steer into the target regardless

[1, Def. 7]: the time-point maximal backward reachable set `R^{∃∀}(-t)`. A
state `x₀` is in it when some admissible input signal drives the perturbed
run into `Xend` at time `t` whatever admissible disturbance occurs — the
states the target is reachable from despite the worst case.

`∃x` inside `∀w`, not `∀x`: quantifying the run itself universally would hold
vacuously for a `w` no `PerturbedTrajectory` witnesses at all — a gap the
derivative-everywhere predicate can leave open, per its own docstring — and
would silently enlarge the set. Existential `x` asks for an actual run, the
same reading `backReachSetForallExists` and `reachSet` both use.

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

/-- Every state from which some admissible input steers the perturbed run into
`Xend` at time `t`, whatever admissible disturbance occurs. -/
def LinearSys.backReachSetExistsForall (sys : LinearSys 𝕋 n) (T : Set ℝ) (U W Xend : S n)
    (t : ℝ) : Set (Vec ℝ n) :=
  {x₀ | ∃ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) ∧
      ∀ w : ℝ → Vec ℝ n, (∀ s ∈ T, w s ∈ construct W) →
        ∃ x : ℝ → Vec ℝ n, sys.PerturbedTrajectory T U W x u w ∧
          x 0 = x₀ ∧ x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

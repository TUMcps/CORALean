import CORALean.ContDynamics.LinearSys.PerturbedTrajectory

/-!
# The states one admissible input can steer into the target over an interval

[1, Def. 7]: the time-interval maximal backward reachable set `R^{∃∀}(-τ)`,
which requires the run to pass through `Xend` at *some* time in `τ`, not at
every time in it, mirroring `timeIntervalBackReachSetForallExists`'s reading
of the same phrase in Def. 6.

`U` and `W` are admissible over the whole of `T`, for the reason given there:
`u(·)` is fixed before `t` is chosen, so its domain cannot already depend on
`t`.

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

/-- Every state from which some admissible input steers the perturbed run
through `Xend` at some time in `τ`, whatever admissible disturbance occurs. -/
def LinearSys.timeIntervalBackReachSetExistsForall (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (U W Xend : S n) (τ : Set ℝ) : Set (Vec ℝ n) :=
  {x₀ | ∃ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) ∧
      ∀ w : ℝ → Vec ℝ n, (∀ s ∈ T, w s ∈ construct W) →
        ∃ x : ℝ → Vec ℝ n, sys.PerturbedTrajectory T U W x u w ∧
          x 0 = x₀ ∧ ∃ t ∈ τ, x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

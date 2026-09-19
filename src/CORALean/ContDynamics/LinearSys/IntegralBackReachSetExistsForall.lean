import CORALean.ContDynamics.LinearSys.PerturbedIntegralTrajectory

/-!
# The maximal backward reachable set, read with Carathéodory runs

[1, Def. 7]'s time-point set `R^{∃∀}(-t)` over `PerturbedIntegralTrajectory`,
the same reading `IntegralBackReachSetForallExists` takes of Def. 6: the `∀w`
guard quantifies over the measurable admissible disturbances, which are the
signals `Z_W(t)` integrates, and no others.

Under the derivative-everywhere reading this set is worse than imprecise: a
pointwise derivative is measurable, so `∀w` there ranges over disturbances no
run realizes at all, and the set collapses to `∅` as soon as `W` holds two
points. `∃x` inside `∀w` rather than `∀x` for the reason
`backReachSetExistsForall` gives: the universal form admits `x₀` vacuously
wherever no run exists.

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

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state from which some admissible input steers the perturbed run into
`Xend` at time `t`, whatever admissible disturbance occurs. -/
def LinearSys.integralBackReachSetExistsForall (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (U W Xend : S n) (t : ℝ) : Set (Vec ℝ n) :=
  {x₀ | ∃ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) ∧
      AEStronglyMeasurable u (volume.restrict T) ∧
      ∀ w : ℝ → Vec ℝ n, (∀ s ∈ T, w s ∈ construct W) →
        AEStronglyMeasurable w (volume.restrict T) →
        ∃ x : ℝ → Vec ℝ n, sys.PerturbedIntegralTrajectory T U W x u w ∧
          x 0 = x₀ ∧ x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

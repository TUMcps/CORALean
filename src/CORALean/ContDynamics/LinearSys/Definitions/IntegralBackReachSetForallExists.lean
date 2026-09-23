import CORALean.ContDynamics.LinearSys.Definitions.PerturbedIntegralTrajectory

/-!
# The minimal backward reachable set, read with Carathéodory runs

[1, Def. 6]'s time-point set `R^{∀∃}(-t)` over `PerturbedIntegralTrajectory`
instead of `PerturbedTrajectory`, exactly as `integralReachSet` reads
`reachSet`: the paper's `U` and `W` are the signals for which the solution
`ξ(t;x₀,u(·),w(·))` exists at all, and for a linear system that is the
measurable bounded ones — the derivative-everywhere reading admits strictly
fewer, which is what turns [1, Prop. 3] from an equality into an inclusion.

So the `∀u` guard carries measurability as well as admissibility: it quantifies
over the same signals `Z_U(t)` integrates, no more and no fewer.

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

/-- Every state that cannot avoid `Xend` at time `t`: for every admissible
input there is some admissible disturbance whose run lands there. -/
def LinearSys.integralBackReachSetForallExists (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (U W Xend : S n) (t : ℝ) : Set (Vec ℝ n) :=
  {x₀ | ∀ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) →
      AEStronglyMeasurable u (volume.restrict T) →
      ∃ w x : ℝ → Vec ℝ n, sys.PerturbedIntegralTrajectory T U W x u w ∧
        x 0 = x₀ ∧ x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

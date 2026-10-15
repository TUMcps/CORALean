module

public import CORALean.ContDynamics.LinearSys.Definitions.IsPerturbedTrajectory

@[expose] public section

/-!
# The backward reachable set under one fixed input trajectory

`R^∃(-τ;u*(·))`, the set [1, Thm. 1]'s development displays: the states some
admissible disturbance drives into `Xend` at some time of `τ` when the input
is held at one chosen signal `u*(·)`. Dropping the `∀u` leaves a set of the
time-inverted forward kind, which is what makes it computable by propagation.

Its point is the identity the theorem opens with: `R^{∀∃}(-τ)` is the
intersection of these sets over all admissible `u*(·)`, so intersecting over
only finitely many of them can only grow the set — the first `⊆` of the proof.

Nothing here quantifies over `u*(·)`, so its own measurability is a
hypothesis of whoever supplies it.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some admissible disturbance drives into `Xend` at some time of
`τ`, the input being held at the one signal `u`. -/
def LinearSys.timeIntervalBackReachSetOfInput (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (U W Xend : S n) (τ : Set ℝ) (u : ℝ → Vec ℝ n) : Set (Vec ℝ n) :=
  {x₀ | ∃ w x : ℝ → Vec ℝ n, sys.IsPerturbedTrajectory T U W x u w ∧
      x 0 = x₀ ∧ ∃ t ∈ τ, x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

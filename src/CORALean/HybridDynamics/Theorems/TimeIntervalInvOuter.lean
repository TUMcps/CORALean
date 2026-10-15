module

public import CORALean.HybridDynamics.Operations.TimeIntervalStepInv
public import CORALean.HybridDynamics.Theorems.FlowOuter

@[expose] public section

/-!
# A stay is enclosed by the invariant-cut time-interval step

`timeInterval_outer` restated against `timeIntervalStepInv`: the invariant
holds of every state of the stay, `x t ∈ construct ℓ.inv`, so `Intersection.intersection_outer`
cuts the enclosure `timeInterval_outer` already gives down to it. The cut lands
on the sum with `Ud`, not on `timeIntervalStep` alone — the invariant is a fact
about `x t`, not about the homogeneous part in isolation.

The continuous reachable set within a location, up to where it would leave the
invariant: the first half of [1, Alg. 5], `jumpIntersection` and its theorems
the second.

`Intersection.intersection` is homogeneous, so this is one of the two places that ask a location's
invariant to be in the state's own family, `Location S S L 𝕋 n` (#39).

It is also the loop body of [2, Alg. 1].

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
* [2] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Intersection (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a stay passes through lies in the location's invariant-cut
time-interval enclosure, the initial set and the input contribution named by
the caller. -/
theorem Location.IsTrajectory.timeIntervalInv_outer [∀ n, OfPoint (S n) (Vec ℝ n)]
    {ℓ : Location S S L 𝕋 n} {τ : ℝ}
    {x : ℝ → Vec ℝ n} {u w} (traj : ℓ.IsTrajectory τ x u w) {R₀ Ud : S n}
    (h₀ : x 0 ∈ construct R₀) (hτ : 0 < τ) {m : ℕ}
    (hε : ‖τ • toRealMat ℓ.dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htτ : t ≤ τ) (hU : Bornology.IsBounded (construct ℓ.inputSet))
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat ℓ.dynamics.A) *ᵥ
      (toRealMat ℓ.dynamics.B *ᵥ u s + toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w s))
      ∈ construct Ud) :
    x t ∈ construct (ℓ.timeIntervalStepInv τ (m + 2) R₀ Ud) :=
  Intersection.intersection_outer _ _ ⟨traj.timeInterval_outer h₀ hτ hε ht0 htτ hU hUd,
    traj.invariant t ⟨ht0, htτ⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

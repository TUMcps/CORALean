module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Topology.Instances.Matrix
public import CORALean.HybridDynamics.Definitions.Location

@[expose] public section

/-!
# A stay in a location is a run of its canonical form

`Location.IsTrajectory` runs the whole equation `ẋ = A x + B u + c + E w`;
`LinearSys.IsCanonicalTrajectory` runs `ẋ = A x + u'`, anchored at a set and with no invariant,
both by the integral equation. A stay is a run of the latter with the combined input `u' = B u + c
+ E w`, CORA's `canonicalForm`, wherever the caller's set `U'` holds every value it takes: at
`ℓ.inputSet` (`memInputSet`) or its float counterpart. The invariant is dropped, as it only ever
tightens an enclosure. The time domain is `Set.Icc 0 τ` on the location's own clock.

## Inputs
* `ℓ` – location
* `τ` – stay duration
* `x` – trajectory of the stay
* `u` – input trajectory
* `w` – disturbance trajectory
* `R₀` – initial set
* `U'` – set holding the combined input

## Hypotheses
* `traj` – the curves are a stay of the location
* `h₀` – initial state lies in the initial set
* `hU'` – combined input stays in the set

## Conclusion
* the stay is a canonical trajectory of the dynamics
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stay read as a run of the location's canonical form, starting in any set that holds its
initial point, its combined input `B u + c + E w` in any set that holds it. -/
theorem Location.IsTrajectory.linearSys {ℓ : Location S G L 𝕋 n} {τ : ℝ} {x : ℝ → Vec ℝ n}
    {u : ℝ → Vec ℝ ℓ.dynamics.m} {w : ℝ → Vec ℝ ℓ.dynamics.r} (traj : ℓ.IsTrajectory τ x u w)
    {R₀ U' : S n} (h₀ : x 0 ∈ construct R₀)
    (hU' : ∀ t ∈ Set.Icc 0 τ, toRealMat ℓ.dynamics.B *ᵥ u t + toRealVec ℓ.dynamics.c +
      toRealMat ℓ.dynamics.E *ᵥ w t ∈ construct U') :
    ℓ.dynamics.IsCanonicalTrajectory (Set.Icc 0 τ) R₀ U' x
      (fun t => toRealMat ℓ.dynamics.B *ᵥ u t + toRealVec ℓ.dynamics.c +
        toRealMat ℓ.dynamics.E *ᵥ w t) where
  init := h₀
  input := hU'
  -- the combined input is the integrand less the continuous drift `A x`
  meas := by
    have hA : Continuous fun v : Vec ℝ n => toRealMat ℓ.dynamics.A *ᵥ v :=
      continuous_const.matrix_mulVec continuous_id
    refine (traj.meas.sub ((hA.comp_continuousOn traj.cont).aestronglyMeasurable
      measurableSet_Icc)).congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Pi.sub_apply, Function.comp_apply]
    abel
  cont := traj.cont
  -- the same integrand, bracketed as `A x + (B u + c + E w)`
  flow t ht := by
    rw [traj.flow t ht]
    simp only [add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

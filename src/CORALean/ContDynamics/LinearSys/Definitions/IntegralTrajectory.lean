import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# Continuous-time linear systems: the integral-equation run

`Trajectory` asks for a derivative at every point of `T`, two-sided wherever
`T` is — stronger than [1, Def. 3.1]'s own solution concept, Sontag's
Carathéodory one (*Math. Control Theory*, 2nd ed., Def. C.2.1), chosen so a
discontinuous (piecewise-constant) input is admissible. `IntegralTrajectory`
states the integral equation that concept solves — plus `cont`, Def. C.2.1's
own "locally absolutely continuous": `intervalIntegral` is junk-valued off
integrability, so without it `flow` alone would admit `x` nothing like a run.

`meas` is the input's own regularity, matching `inputReach`'s "measurable
enough to integrate, no more", restricted to `T` since that is all `flow`
ever integrates over.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       15-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory intervalIntegral

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- The integral-equation counterpart of `Trajectory`: the same initial and input
conditions, with the flow stated as `x t = x 0 + ∫₀ᵗ (A x + u)` rather than as a
derivative, so a run whose input jumps still satisfies it. -/
structure LinearSys.IntegralTrajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  meas : AEStronglyMeasurable u (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) :
    x t = x 0 + ∫ s in (0:ℝ)..t, (toRealMat sys.A *ᵥ x s + u s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

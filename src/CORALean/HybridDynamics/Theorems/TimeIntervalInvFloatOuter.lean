module

public import CORALean.ContSet.HPolytope.Float.Instances
public import CORALean.ContSet.HPolytope.Float.Theorems.ContractBoxOuter
public import CORALean.HybridDynamics.Operations.TimeIntervalInvFloat
public import CORALean.HybridDynamics.Theorems.FlowOuterFloat
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# A stay is enclosed by the invariant-cut float step

`timeIntervalInv_outer` at a float zonotope: the state lies in the float step
plus `Ud` by `timeIntervalFloat_outer`, so in its box, and in the invariant by
`IsTrajectory.invariant`, so in the box cut by the invariant's rows.

## Inputs
* `ℓ` – location
* `τ` – stay duration
* `x` – trajectory of the stay
* `u` – input trajectory
* `w` – disturbance trajectory
* `R₀` – initial set
* `Ud` – input contribution set
* `r` – time step
* `η` – Taylor order
* `t` – time within the stay

## Hypotheses
* `traj` – the curves are a stay of the location
* `h₀` – initial state lies in the initial set
* `hr` – time step positive
* `hη` – Taylor order admissible at the step
* `ht0` – time nonnegative
* `htτ` – time within the stay duration
* `htr` – time within the time step
* `hUd` – input contribution holds the particular integral

## Conclusion
* state at the time lies in the invariant-cut float step
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a stay passes through by time `r` lies in the float step from
`R₀` plus `Ud`, cut to the location's invariant. -/
theorem Location.IsTrajectory.timeIntervalInvFloat_outer
    {ℓ : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n} {τ : ℝ}
    {x : ℝ → Vec ℝ n} {u w}
    (traj : ℓ.IsTrajectory τ x u w) {R₀ Ud : Zonotope (Vec 𝕋 n)} (h₀ : x 0 ∈ construct R₀) {r : 𝕋}
    {η : ℕ} (hr : 0 < toReal r) (hη : ℓ.dynamics.OrderAdmissibleFloat r r η) {t : ℝ}
    (ht0 : 0 ≤ t) (htτ : t ≤ τ) (htr : t ≤ toReal r)
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • Scalar.toRealMat ℓ.dynamics.A) *ᵥ
      (Scalar.toRealMat ℓ.dynamics.B *ᵥ u s + Scalar.toRealVec ℓ.dynamics.c +
        Scalar.toRealMat ℓ.dynamics.E *ᵥ w s))
      ∈ construct Ud) :
    x t ∈ construct (ℓ.timeIntervalInvFloat r η R₀ Ud) :=
  Interval.zonotope_contains _ (ℓ.inv.contractBox_outer _
    ⟨Zonotope.interval_contains _ (traj.timeIntervalFloat_outer h₀ hr hη ht0 htτ htr hUd),
      traj.invariant t ⟨ht0, htτ⟩⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

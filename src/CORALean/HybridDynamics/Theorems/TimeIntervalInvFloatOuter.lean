module

public import CORALean.ContSet.HPolytope.Float.Instances
public import CORALean.ContSet.HPolytope.Float.Theorems.ContractBoxOuter
public import CORALean.HybridDynamics.Operations.TimeIntervalStepInvFloat
public import CORALean.HybridDynamics.Theorems.FlowOuterFloat

@[expose] public section

/-!
# A stay is enclosed by the invariant-cut float step

`timeIntervalInv_outer` at a float zonotope: the state lies in the float step
plus `Ud` by `timeIntervalFloat_outer`, so in its box, and in the invariant by
`Trajectory.invariant`, so in the box cut by the invariant's rows.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
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
theorem Location.Trajectory.timeIntervalInvFloat_outer
    {ℓ : Location (fun k => Zonotope (Vec 𝕋 k)) (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n} {τ : ℝ}
    {x u : ℝ → Vec ℝ n}
    (traj : ℓ.Trajectory τ x u) {R₀ Ud : Zonotope (Vec 𝕋 n)} (h₀ : x 0 ∈ construct R₀) {r : 𝕋}
    {η : ℕ} (hr : 0 < toReal r) (hη : ℓ.dynamics.OrderAdmissibleFloat r r η) {t : ℝ}
    (ht0 : 0 ≤ t) (htτ : t ≤ τ) (htr : t ≤ toReal r)
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • Scalar.toRealMat ℓ.dynamics.A) *ᵥ u s)
      ∈ construct Ud) :
    x t ∈ construct (ℓ.timeIntervalStepInvFloat r η R₀ Ud) :=
  Interval.zonotope_contains _ (ℓ.inv.contractBox_outer _
    ⟨Zonotope.interval_contains _ (traj.timeIntervalFloat_outer h₀ hr hη ht0 htτ htr hUd),
      traj.invariant t ⟨ht0, htτ⟩⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

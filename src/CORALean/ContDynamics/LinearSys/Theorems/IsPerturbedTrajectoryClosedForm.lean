module

public import CORALean.ContDynamics.LinearSys.Definitions.IsPerturbedTrajectory
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormContinuousOn
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormFlow
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableMulVecAdd
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableOfMemBounded

@[expose] public section

/-!
# Any admissible pair of signals is realized by a perturbed run

The converse of `PerturbedSuperposition`, and what the `⊇` halves of
[1, Prop. 3] and [1, Prop. 5] need: given a measurable input and a measurable
disturbance, the sum of the two closed forms — one started at `x₀`, one at the
origin — is a `IsPerturbedTrajectory` carrying exactly those two signals.

Summing two one-signal closed forms rather than forming `closedForm x₀ (u + w)`
keeps every hypothesis at `U` or at `W` separately: the folded input would need
a representation denoting `U ⊕ W`, which `Plus` only ever encloses.

## Inputs
* `sys` – linear system
* `U` – input set
* `W` – disturbance set
* `t` – time
* `x₀` – initial point
* `u` – input signal
* `w` – disturbance signal

## Hypotheses
* `ht` – time nonnegative
* `hU` – input set bounded
* `hW` – disturbance set bounded
* `hu` – input values lie in the set
* `humeas` – input measurable
* `hw` – disturbance values lie in the set
* `hwmeas` – disturbance measurable

## Conclusion
* the sum of the two closed forms is a perturbed trajectory

## References

* [1] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The sum of the two closed forms is a perturbed run at the given input and
disturbance, starting from `x₀`. -/
theorem LinearSys.isPerturbedTrajectory_closedForm (sys : LinearSys 𝕋 n) {U W : S n}
    {t : ℝ} (ht : 0 ≤ t) (hU : Bornology.IsBounded (construct U))
    (hW : Bornology.IsBounded (construct W)) (x₀ : Vec ℝ n) {u w : ℝ → Vec ℝ n}
    (hu : ∀ s ∈ Set.Icc (0:ℝ) t, u s ∈ construct U)
    (humeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 t)))
    (hw : ∀ s ∈ Set.Icc (0:ℝ) t, w s ∈ construct W)
    (hwmeas : AEStronglyMeasurable w (volume.restrict (Set.Icc 0 t))) :
    sys.IsPerturbedTrajectory (Set.Icc 0 t) U W
      (fun τ => sys.closedForm x₀ u τ + sys.closedForm 0 w τ) u w where
  input := hu
  disturbance := hw
  measInput := humeas
  measDisturbance := hwmeas
  cont := (sys.closedForm_continuousOn x₀ ht hU hu humeas).add
    (sys.closedForm_continuousOn 0 ht hW hw hwmeas)
  flow τ hτ := by
    set A := toRealMat sys.A
    have huint : IntervalIntegrable u volume 0 t :=
      intervalIntegrable_of_mem_bounded ht hU hu humeas
    have hwint : IntervalIntegrable w volume 0 t :=
      intervalIntegrable_of_mem_bounded ht hW hw hwmeas
    have h₁ : IntervalIntegrable (fun ρ => A *ᵥ sys.closedForm x₀ u ρ + u ρ) volume 0 τ :=
      intervalIntegrable_mulVec_add A (sys.closedForm_continuousOn x₀ ht hU hu humeas) huint ht hτ
    have h₂ : IntervalIntegrable (fun ρ => A *ᵥ sys.closedForm 0 w ρ + w ρ) volume 0 τ :=
      intervalIntegrable_mulVec_add A (sys.closedForm_continuousOn 0 ht hW hw hwmeas) hwint ht hτ
    -- the two flow equations added, their integrands recombined under one integral
    have hadd : (∫ ρ in (0:ℝ)..τ, (A *ᵥ sys.closedForm x₀ u ρ + u ρ))
        + (∫ ρ in (0:ℝ)..τ, (A *ᵥ sys.closedForm 0 w ρ + w ρ))
        = ∫ ρ in (0:ℝ)..τ,
            (A *ᵥ (sys.closedForm x₀ u ρ + sys.closedForm 0 w ρ) + u ρ + w ρ) := by
      rw [← intervalIntegral.integral_add h₁ h₂]
      refine intervalIntegral.integral_congr fun ρ _ => ?_
      show (A *ᵥ sys.closedForm x₀ u ρ + u ρ) + (A *ᵥ sys.closedForm 0 w ρ + w ρ)
        = A *ᵥ (sys.closedForm x₀ u ρ + sys.closedForm 0 w ρ) + u ρ + w ρ
      rw [Matrix.mulVec_add]
      abel
    show sys.closedForm x₀ u τ + sys.closedForm 0 w τ
      = sys.closedForm x₀ u 0 + sys.closedForm 0 w 0
        + ∫ ρ in (0:ℝ)..τ, (A *ᵥ (sys.closedForm x₀ u ρ + sys.closedForm 0 w ρ) + u ρ + w ρ)
    rw [← hadd, sys.closedForm_flow x₀ ht hU hu humeas hτ,
      sys.closedForm_flow 0 ht hW hw hwmeas hτ]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

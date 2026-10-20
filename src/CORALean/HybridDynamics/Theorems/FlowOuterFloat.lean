module

public import CORALean.HybridDynamics.Theorems.Basic
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.HybridDynamics.Operations.TimeIntervalStepFloat
public import CORALean.HybridDynamics.Theorems.LinearEmbedding

@[expose] public section

/-!
# A stay is enclosed by the float time-interval step

`timeInterval_outer` with the float step in place of the exact one: the
variation of constants splits `x t` into the free motion, which
`timeIntervalStepFloat_outer` places in the float step at an order admissible
for `[r, r]`, and the input's contribution, which the caller's `Ud` holds. The
stay need not last `r`: any `t ≤ r` it reaches is covered.

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
* state at the time lies in the float step plus the input contribution
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a stay passes through by time `r` lies in the float step from
`R₀` plus the input contribution `Ud` named by the caller. -/
theorem Location.IsTrajectory.timeIntervalFloat_outer
    {ℓ : Location 𝒵[𝕋] G L 𝕋 n}
    {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} (traj : ℓ.IsTrajectory τ x u w) {R₀ Ud : Zonotope (Vec 𝕋 n)}
    (h₀ : x 0 ∈ construct R₀) {r : 𝕋} {η : ℕ} (hr : 0 < toReal r)
    (hη : ℓ.dynamics.OrderAdmissibleFloat r r η) {t : ℝ} (ht0 : 0 ≤ t) (htτ : t ≤ τ)
    (htr : t ≤ toReal r)
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • Scalar.toRealMat ℓ.dynamics.A) *ᵥ
      (Scalar.toRealMat ℓ.dynamics.B *ᵥ u s + Scalar.toRealVec ℓ.dynamics.c +
        Scalar.toRealMat ℓ.dynamics.E *ᵥ w s))
      ∈ construct Ud) : -- --- CONCL ---
    x t ∈ construct (Plus.plus (ℓ.timeIntervalStepFloat r η R₀) Ud) := by -- --- PROOF ---
  have ltraj := traj.linearSys h₀ traj.inputSetFloat_mem
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 τ := Set.Icc_subset_Icc le_rfl htτ
  -- the variation of constants, from `0` to `t`
  have hvoc := ltraj.variation_of_constants hTt le_rfl ht0
    (CompactSet.isBounded_construct ℓ.inputSetFloat)
  rw [sub_zero] at hvoc
  rw [hvoc]
  exact Plus.plus_outer _ _ (Set.add_mem_add
    (ℓ.dynamics.timeIntervalStepFloat_outer hr hη R₀ h₀ ht0 htr) hUd)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

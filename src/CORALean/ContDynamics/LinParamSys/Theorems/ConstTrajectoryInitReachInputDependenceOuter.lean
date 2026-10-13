module

public import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.InitReachInputDependenceOuter
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.ContSet.Theorems.IsBoundedConstruct

@[expose] public section

/-!
# A run with a parameter-dependent constant input stays in the corrected first step

`LinParamSys.ConstTrajectory.initReachInputDependence_outer`: `initReachInputDependence_outer`
for a `'constParam'` run whose matrix is `A(p) = A_c + Σ pᵢ A_g⁽ⁱ⁾` and whose input is the
constant `u(p) = U_c + Σ pᵢ U_G⁽ⁱ⁾` at the same `p`. The run is the point system's
(`toLinearSys`), so variation of constants gives it in closed form, the input integral being
the constant's on `[0, t]`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A constant-parameter run whose matrix and constant input share the parameter `p` is at the
end of the step in the time-point set and at every time of it in the time-interval set. -/
theorem LinParamSys.ConstTrajectory.initReachInputDependence_outer {sys : LinParamSys 𝕄𝒵 n}
    {T : Set ℝ} {Rinit : Zonotope (Vec ℝ n)} {Uc : Vec ℝ n} {UG : Fin sys.A.h → Vec ℝ n}
    {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n}
    (traj : sys.ConstTrajectory (S := 𝒵) T Rinit (⟨sys.A.h, Uc, UG⟩ : Zonotope (Vec ℝ n)) x u A)
    {p : Fin sys.A.h → ℝ} (hp : ∀ i, |p i| ≤ 1) (hA : A = sys.A.c + ∑ i, p i • sys.A.G i)
    (hu : ∀ s ∈ T, u s = Uc + ∑ i, p i • UG i)
    {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A.interval).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    x r ∈ construct (sys.initReachInputDependence r (m + 2) Rinit Uc UG).1 ∧
      x t ∈ construct (sys.initReachInputDependence r (m + 2) Rinit Uc UG).2 := by -- --- PROOF ---
  have trajL := traj.toLinearSys
  have hU : Bornology.IsBounded
      (construct (⟨sys.A.h, Uc, UG⟩ : Zonotope (Vec ℝ n))) :=
    CompactSet.isBounded_construct _
  -- each time as variation of constants, the input the constant `u(p)`
  have hclosed : ∀ τ, 0 ≤ τ → τ ≤ r → x τ = exp (τ • A) *ᵥ x 0
      + ∫ s in (0:ℝ)..τ, exp ((τ - s) • A) *ᵥ (Uc + ∑ i, p i • UG i) := by
    intro τ hτ0 hτr
    have hvoc := trajL.variation_of_constants ((Set.Icc_subset_Icc_right hτr).trans hT)
      le_rfl hτ0 hU
    simp only [sub_zero, Scalar.toRealMat_real] at hvoc
    rw [hvoc]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hτ0] at hs
    simp only [hu s (hT ⟨hs.1, hs.2.trans hτr⟩)]
  have h := sys.initReachInputDependence_outer hr hε Rinit Uc UG hp traj.init ht0 htr
  subst hA
  rw [hclosed r hr.le le_rfl, hclosed t ht0 htr]
  exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

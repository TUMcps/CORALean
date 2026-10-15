module

public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryCanonical
public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.InitReachInputDependenceOuter
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A run with a parameter-dependent constant input stays in the corrected first step

`LinParamSys.IsConstTrajectory.initReachInputDependence_outer`:
`initReachInputDependence_outer` for a `'constParam'` run whose matrix is
`A(p) = A_c + Σ pᵢ A_g⁽ⁱ⁾` and whose input is the constant `u(p) = U_c + Σ pᵢ U_G⁽ⁱ⁾`, in input
coordinates, at the same `p`. `initReachInputDependence` reads `B` at its center, so the run's
`B` is that center. The run is a run of the canonical form at the state-space input `B u + c`
(`IsConstTrajectory.canonical`), the point system's (`toLinearSys`), so variation of constants
gives it in closed form, the input integral being the constant's on `[0, t]`.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
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
theorem LinParamSys.IsConstTrajectory.initReachInputDependence_outer {sys : LinParamSys 𝕄𝒵 n}
    {T : Set ℝ} {Rinit : Zonotope (Vec ℝ n)} {Uc : Vec ℝ sys.m} {UG : Fin sys.A.h → Vec ℝ sys.m}
    {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ sys.m} {A : Mat ℝ n n} {B : Mat ℝ n sys.m}
    (traj : sys.IsConstTrajectory (S := 𝒵) T Rinit (⟨sys.A.h, Uc, UG⟩ : Zonotope (Vec ℝ sys.m))
        x u A B)
    {p : Fin sys.A.h → ℝ} (hp : ∀ i, |p i| ≤ 1) (hA : A = sys.A.c + ∑ i, p i • sys.A.G i)
    (hB : B = sys.B.c) (hu : ∀ s ∈ T, u s = Uc + ∑ i, p i • UG i)
    {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A.interval).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    x r ∈ construct (sys.initReachInputDependence r (m + 2) Rinit Uc UG).1 ∧
      x t ∈ construct (sys.initReachInputDependence r (m + 2) Rinit Uc UG).2 := by -- --- PROOF ---
  -- the combined input `B u + c` is the state-space constant `u(p)` carries
  have hv : ∀ s ∈ T, B *ᵥ u s + sys.c = (sys.B.c *ᵥ Uc + sys.c) + ∑ i, p i • (sys.B.c *ᵥ UG i) := by
    intro s hs
    simp only [hB, hu s hs, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul]
    abel
  have trajC := traj.canonical (U' := (⟨sys.A.h, sys.B.c *ᵥ Uc + sys.c,
    fun i => sys.B.c *ᵥ UG i⟩ : Zonotope (Vec ℝ n))) fun s hs => ⟨p, hp, hv s hs⟩
  have trajL := trajC.toLinearSys
  have hU : Bornology.IsBounded (construct
      (⟨sys.A.h, sys.B.c *ᵥ Uc + sys.c, fun i => sys.B.c *ᵥ UG i⟩ : Zonotope (Vec ℝ n))) :=
    CompactSet.isBounded_construct _
  -- each time as variation of constants, the input the constant `B u(p) + c`
  have hclosed : ∀ τ, 0 ≤ τ → τ ≤ r → x τ = exp (τ • A) *ᵥ x 0
      + ∫ s in (0:ℝ)..τ, exp ((τ - s) • A) *ᵥ (sys.B.c *ᵥ (Uc + ∑ i, p i • UG i) + sys.c) := by
    intro τ hτ0 hτr
    have hvoc := trajL.variation_of_constants ((Set.Icc_subset_Icc_right hτr).trans hT)
      le_rfl hτ0 hU
    simp only [sub_zero, Scalar.toRealMat_real] at hvoc
    rw [hvoc]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hτ0] at hs
    simp only [hB, hu s (hT ⟨hs.1, hs.2.trans hτr⟩)]
  have h := sys.initReachInputDependence_outer hr hε Rinit Uc UG hp traj.init ht0 htr
  subst hA
  rw [hclosed r hr.le le_rfl, hclosed t ht0 htr]
  exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CurvatureEnclosureFloat
public import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.Operations.AffineWindowFloat

@[expose] public section

/-!
# The float affine window holds the affine flow over the step

A point `h` of `H(t_k)` under the constant input `ũ` is, after any `τ ∈ [0, Δt]`, at
`e^{τA}h + ∫₀^τ e^{Aσ}dσ ũ`. It is the straight-line point
`(1 - τ/Δt) h + (τ/Δt) h'`, `h' = e^{ΔtA}h + ∫₀^Δt e^{Aσ}dσ ũ`, plus the curvature deviation:
the first is in `comb(H, H(t_{k+1}))` whenever `h'` is in `H(t_{k+1})`, and the second in `C`
(`curvatureEnclosure_outer`).

## Inputs
* `sys` – linear system
* `H` – float state zonotope
* `Hnext` – float next state zonotope
* `ũ` – float constant input
* `Δt` – float step length
* `η` – Taylor order
* `h` – state point
* `τ` – time

## Hypotheses
* `hΔt` – step length positive
* `hη` – order admissible
* `hh` – point lies in the zonotope
* `hnext` – next zonotope holds the state after the step
* `hτ0` – time nonnegative
* `hτ` – time within the step

## Conclusion
* the affine flow state at the time lies in the float window
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.affineWindowFloat_outer (sys : LinearSys 𝕋 n) {H Hnext : Zonotope (Vec 𝕋 n)}
    {ũ : Vec 𝕋 n} {Δt : 𝕋} {η : ℕ} (hΔt : 0 < toReal Δt)
    (hη : sys.OrderAdmissibleFloat Δt Δt η) {h : Vec ℝ n} (hh : h ∈ H.construct)
    (hnext : exp (toReal Δt • Scalar.toRealMat sys.A) *ᵥ h
      + Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt) *ᵥ toRealVec ũ
        ∈ Hnext.construct) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ toReal Δt) : -- --- CONCL ---
    exp (τ • Scalar.toRealMat sys.A) *ᵥ h
        + Real.MatExp.expIntegral (Scalar.toRealMat sys.A) τ *ᵥ toRealVec ũ
      ∈ (sys.affineWindowFloat H Hnext ũ Δt η).construct := by -- --- PROOF ---
  set A := Scalar.toRealMat sys.A with hA
  set lam := τ / toReal Δt with hlam
  have hl0 : 0 ≤ lam := div_nonneg hτ0 hΔt.le
  have hl1 : lam ≤ 1 := (div_le_one hΔt).mpr hτ
  have hcurv := MatExp.curvatureEnclosure_outer (Interval.point sys.A) (H := H) (ũ := ũ) hΔt
    hη.1 hη.2 (Interval.mem_point sys.A) hh hτ0 hτ
  -- the straight-line point is in the comb, the curvature deviation in `C`
  have hcomb : (1 - lam) • h + lam • (exp (toReal Δt • A) *ᵥ h
      + Real.MatExp.expIntegral A (toReal Δt) *ᵥ toRealVec ũ)
      ∈ (LinComb.linComb H Hnext).construct :=
    LinComb.linComb_outer H Hnext
      ⟨h, hh, _, hnext, 1 - lam, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
  -- and the two add up to the flow at `τ`
  have heq : exp (τ • A) *ᵥ h + Real.MatExp.expIntegral A τ *ᵥ toRealVec ũ
      = ((1 - lam) • h + lam • (exp (toReal Δt • A) *ᵥ h
          + Real.MatExp.expIntegral A (toReal Δt) *ᵥ toRealVec ũ))
        + ((exp (τ • A) - 1 - lam • (exp (toReal Δt • A) - 1)) *ᵥ h
          + (Real.MatExp.expIntegral A τ - lam • Real.MatExp.expIntegral A (toReal Δt))
            *ᵥ toRealVec ũ) := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    module
  rw [heq]
  exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hcomb hcurv)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

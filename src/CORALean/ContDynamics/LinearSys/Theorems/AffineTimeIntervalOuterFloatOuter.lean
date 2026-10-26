module

public import CORALean.ContDynamics.LinearSys.Operations.AffineTimeIntervalOuterFloat
public import CORALean.ContDynamics.LinearSys.Operations.AffineTimePointNextFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContDynamics.LinearSys.Theorems.AffineWindowFloatOuter

@[expose] public section

/-!
# The float affine time-interval set holds the affine flow over the step

`affineWindowFloat_outer` at `H(t_{k+1}) = [e^{AΔt}] H ⊕ P^u(Δt)`, which holds the flow's
value one step on (`aux_affineTimePointNextFloat_outer`): a point of `H(t_k)` under the constant
input `ũ` is, after any `τ ∈ [0, Δt]`, in `affineTimeIntervalOuterFloat`.

## Inputs
* `sys` – linear system
* `H` – float state zonotope
* `ũ` – float constant input
* `Δt` – float step length
* `η` – Taylor order
* `h` – state point
* `τ` – time

## Hypotheses
* `hΔt` – step length positive
* `hη` – order admissible
* `hh` – point lies in the zonotope
* `hτ0` – time nonnegative
* `hτ` – time within the step

## Conclusion
* the affine flow state at the time lies in the float time-interval set
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open MeasureTheory Pointwise
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- At `Δt > 0` and an admissible `η`, `e^{AΔt} h + ∫₀^Δt e^{Aσ}dσ ũ` is in the float
`H(t_{k+1})` for every `h` the float `H(t_k)` holds. -/
private theorem LinearSys.aux_affineTimePointNextFloat_outer (sys : LinearSys 𝕋 n)
    {H : Zonotope (Vec 𝕋 n)} {ũ : Vec 𝕋 n} {Δt : 𝕋} {η : ℕ} (hΔt : 0 < toReal Δt)
    (hη : sys.IsOrderAdmissibleFloat Δt Δt η) {h : Vec ℝ n} (hh : h ∈ H.construct)
        : -- --- CONCL ---
    exp (toReal Δt • Scalar.toRealMat sys.A) *ᵥ h
        + Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt) *ᵥ toRealVec ũ
      ∈ (sys.affineTimePointNextFloat H ũ Δt η).construct := by -- --- PROOF ---
  -- `e^{AΔt} h` in `[e^{AΔt}] H`
  have hexp := sys.exp_mem_expIntervalFloat hη le_rfl le_rfl
  have hmt := Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋])
    (sys.expIntervalFloat Δt Δt η) H (Set.mem_biUnion hexp (Set.mem_image_of_mem _ hh))
  -- the input held at `ũ` over `[0, Δt]` contributes the constant's share
  have hpt : toRealVec ũ ∈ (Interval.point ũ).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.mem_point ũ)
  have hreach : Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt) *ᵥ toRealVec ũ
      ∈ sys.inputReach (S := 𝒵[𝕋]) (Interval.point ũ).zonotope (toReal Δt) :=
    ⟨fun _ => toRealVec ũ, fun _ _ => hpt, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput _ _ hΔt.le).symm⟩
  exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hmt
    (sys.inputReach_subset_inputSolutionFloat hΔt hη _ hreach))

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.affineTimeIntervalOuterFloat_outer (sys : LinearSys 𝕋 n) {H : Zonotope (Vec 𝕋 n)}
    {ũ : Vec 𝕋 n} {Δt : 𝕋} {η : ℕ} (hΔt : 0 < toReal Δt)
    (hη : sys.IsOrderAdmissibleFloat Δt Δt η) {h : Vec ℝ n} (hh : h ∈ H.construct) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ toReal Δt) :
    exp (τ • Scalar.toRealMat sys.A) *ᵥ h
        + Real.MatExp.expIntegral (Scalar.toRealMat sys.A) τ *ᵥ toRealVec ũ
      ∈ (sys.affineTimeIntervalOuterFloat H ũ Δt η).construct :=
  sys.affineWindowFloat_outer hΔt hη hh (sys.aux_affineTimePointNextFloat_outer hΔt hη hh) hτ0 hτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContDynamics.LinearSys.Operations.AffineTimePointNextFloat
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat

/-!
# `affineTimePointNextFloat` holds `H(t_{k+1})`

Every point `e^{AΔt} h + ∫₀^Δt e^{Aσ}dσ ũ` of the exact `MatExp.affineTimePointNext`, `h` in
the float `H(t_k)`: `e^{AΔt}` is in `[e^{AΔt}]` (`exp_mem_expIntervalFloat`), and the
constant's share is what the input held at `ũ` contributes, which the float input solution of
`{ũ}` holds (`inputReach_subset_inputSolutionFloat`). [1, Alg. 1] lines 6-7.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `Δt > 0` and an admissible `η`, `e^{AΔt} h + ∫₀^Δt e^{Aσ}dσ ũ` is in the float
`H(t_{k+1})` for every `h` the float `H(t_k)` holds. -/
theorem LinearSys.affineTimePointNextFloat_outer (sys : LinearSys 𝕋 n) {H : Zonotope 𝕋 n}
    {ũ : Vec 𝕋 n} {Δt : 𝕋} {η : ℕ} (hΔt : 0 < toReal Δt)
    (hη : sys.OrderAdmissibleFloat Δt Δt η) {h : Vec ℝ n} (hh : h ∈ H.construct) :
    exp (toReal Δt • Scalar.toRealMat sys.A) *ᵥ h
        + Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt) *ᵥ toRealVec ũ
      ∈ (sys.affineTimePointNextFloat H ũ Δt η).construct := by -- --- PROOF ---
  -- `e^{AΔt} h` in `[e^{AΔt}] H`
  have hexp := sys.exp_mem_expIntervalFloat hη le_rfl le_rfl
  have hmt := Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (sys.expIntervalFloat Δt Δt η) H (Set.mem_biUnion hexp (Set.mem_image_of_mem _ hh))
  -- the input held at `ũ` over `[0, Δt]` contributes the constant's share
  have hpt : toRealVec ũ ∈ (Interval.point ũ).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.mem_point ũ)
  have hreach : Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt) *ᵥ toRealVec ũ
      ∈ sys.inputReach (S := Zonotope 𝕋) (Interval.point ũ).zonotope (toReal Δt) :=
    ⟨fun _ => toRealVec ũ, fun _ _ => hpt, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput _ _ hΔt.le).symm⟩
  exact Plus.plus_outer (S := Zonotope 𝕋 n) _ _ (Set.add_mem_add hmt
    (sys.inputReach_subset_inputSolutionFloat hΔt hη _ hreach))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

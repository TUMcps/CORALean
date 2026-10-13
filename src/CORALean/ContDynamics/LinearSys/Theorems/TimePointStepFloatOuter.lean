module

public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat

@[expose] public section

/-!
# `timePointStepFloat` contains the flow at the end of the step

`e^{AΔt}` is in `expIntervalFloat Δt Δt`, and `Mtimes.mtimes_outer` at the float
interval matrix carries every point of `R` through every matrix of the box. No
sign is asked of `Δt`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.timePointStepFloat_outer (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η : ℕ}
    (hη : sys.OrderAdmissibleFloat Δt Δt η) (R : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ R.construct) :
    exp (toReal Δt • Scalar.toRealMat sys.A) *ᵥ x
      ∈ (sys.timePointStepFloat Δt η R).construct :=
  Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k)) _ R
    (Set.mem_biUnion (sys.exp_mem_expIntervalFloat hη le_rfl le_rfl) (Set.mem_image_of_mem _ hx))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

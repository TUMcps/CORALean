import CORALean.ContDynamics.LinParamSys.Operations.InputTermZonoFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
import CORALean.ContSet.Zonotope.Float.Theorems.MatPowOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MatSmulOuter

/-!
# A member's order-`i` input matrix lies in `inputTermZonoFloat`

`matPow_outer` places the member's power, `smul_outer` scales it by the bracketed
coefficient `taylorCoeffBounds_mem` supplies.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.smul_pow_mem_inputTermZonoFloat
    (sys : LinParamSys (fun m n => GZonotope (Mat 𝕋 m n)) n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) (i : ℕ) :
    (toReal r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • A ^ i
      ∈ (sys.inputTermZonoFloat r i).construct := by
  show _ ∈ (GZonotope.matSmul _ _ (sys.A.matPow i)).materialiseMat.construct
  rw [GZonotope.materialiseMat_eq]
  exact GZonotope.matSmul_outer (MatExp.taylorCoeffBounds_mem hr (i + 1)).1
    (MatExp.taylorCoeffBounds_mem hr (i + 1)).2 _ (GZonotope.matPow_outer sys.A hA i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

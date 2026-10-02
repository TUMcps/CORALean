import CORALean.ContDynamics.LinParamSys.Operations.InputTermZonoFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
import CORALean.ContSet.MatZonotope.Float.Theorems.MatPowOuter
import CORALean.ContSet.MatZonotope.Float.Theorems.SmulOuter

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
    (sys : LinParamSys (fun m n => MatZonotope 𝕋 m n) n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) (i : ℕ) :
    (toReal r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • A ^ i
      ∈ (sys.inputTermZonoFloat r i).construct := by
  show _ ∈ (MatZonotope.smul _ _ (sys.A.matPow i)).materialise.construct
  rw [MatZonotope.materialise_eq]
  exact MatZonotope.smul_outer (MatExp.taylorCoeffBounds_mem hr (i + 1)).1
    (MatExp.taylorCoeffBounds_mem hr (i + 1)).2 _ (MatZonotope.matPow_outer sys.A hA i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Taylm.Float.Operations.Cos
import CORALean.ContSet.Taylm.Float.Theorems.ComposeOuter
import CORALean.ContSet.Taylm.Float.Theorems.TrigCoefMem
import CORALean.ContSet.Taylm.Float.Theorems.UnitRemainderLe

/-!
# `Taylm.cos` encloses `cos ∘ f`

`compose_outer` with the Taylor coefficients at the constant part, which `trigCoef_mem`
encloses, and the remainder `unitRemainder_le`, every derivative of `cos` being at most one in
magnitude. No domain condition and no range hypothesis.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.cos_outer (p : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    (T.cos p).Encloses fun t => Real.cos (f t) :=
  Taylm.compose_outer h Real.cos T.constCoef _ _ T.maxOrder _
    (fun k => iteratedDeriv k Real.cos (toReal T.constCoef) / (k.factorial : ℝ))
    (fun k _ => (Taylm.trigCoef_mem p T.constCoef k).2) fun _ ht =>
      Taylm.unitRemainder_le h (fun _ => Real.contDiff_cos.contDiffAt)
        (fun ξ => Real.abs_iteratedDeriv_cos_le_one _ ξ) ht

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

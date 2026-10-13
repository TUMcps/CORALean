module

public import CORALean.ContSet.Taylm.Float.Operations.Sin
public import CORALean.ContSet.Taylm.Float.Theorems.ComposeOuter
public import CORALean.ContSet.Taylm.Float.Theorems.TrigCoefMem
public import CORALean.ContSet.Taylm.Float.Theorems.UnitRemainderLe

@[expose] public section

/-!
# `Taylm.sin` encloses `sin ∘ f`

`compose_outer` with the Taylor coefficients at the constant part, which `trigCoef_mem`
encloses, and the remainder `unitRemainder_le`, every derivative of `sin` being at most one in
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

theorem Taylm.sin_outer (p : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    (T.sin p).Encloses fun t => Real.sin (f t) :=
  Taylm.compose_outer h Real.sin T.constCoef _ _ T.maxOrder _
    (fun k => iteratedDeriv k Real.sin (toReal T.constCoef) / (k.factorial : ℝ))
    (fun k _ => (Taylm.trigCoef_mem p T.constCoef k).1) fun _ ht =>
      Taylm.unitRemainder_le h (fun _ => Real.contDiff_sin.contDiffAt)
        (fun ξ => Real.abs_iteratedDeriv_sin_le_one _ ξ) ht

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

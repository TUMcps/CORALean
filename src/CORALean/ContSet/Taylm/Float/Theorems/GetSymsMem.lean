module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.GetSymsMem

@[expose] public section

/-!
# The stored polynomial brackets the function, over a floating-point scalar

A function the float model encloses lies within the stored remainder interval plus the error box
around its polynomial part `T.nominal.getSyms` on the box: the stored floats read as exact
coefficients, with nothing rounded.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.getSyms_mem {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) {t : Vec ℝ n}
    (ht : t ∈ Real.Taylm.box n) :
    T.nominal.getSyms t + (toReal T.rem.inf + toReal T.I_error.inf) ≤ f t ∧
      f t ≤ T.nominal.getSyms t + (toReal T.rem.sup + toReal T.I_error.sup) :=
  Real.Taylm.getSyms_mem h ht

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

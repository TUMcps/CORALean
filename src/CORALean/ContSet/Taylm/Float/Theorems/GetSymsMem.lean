module

public import CORALean.ContSet.Taylm.Float.Operations.GetSyms
public import CORALean.ContSet.Taylm.Real.Theorems.GetSymsMem

@[expose] public section

/-!
# `Taylm.getSyms` brackets the function, over a floating-point scalar

A function the float model encloses lies within the stored remainder interval around its
polynomial part on the box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.getSyms_mem {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) {t : Vec ℝ n}
    (ht : t ∈ Real.Taylm.box n) :
    T.getSyms t + toReal T.remInf ≤ f t ∧ f t ≤ T.getSyms t + toReal T.remSup :=
  Real.Taylm.getSyms_mem h ht

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

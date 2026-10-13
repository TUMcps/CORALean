module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatBound

@[expose] public section

/-!
# `Interval.boundNegProj`

A box answers the negated coordinate direction with its own lower bound,
negated, exactly.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.boundNegProj (I : Interval (Vec 𝕋 n)) (j : Fin n) :
    FloatBound 𝕋 I.construct (-LinearMap.proj j) :=
  ⟨neg (I.inf j), fun x hx => by
    -- ascribed, `linarith` reading membership no further than reducible defeq
    have h : toReal (I.inf j) ≤ x j := (hx j).1
    show -(x j) ≤ toReal (neg (I.inf j))
    rw [toReal_neg]
    linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

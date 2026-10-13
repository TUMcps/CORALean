module

public import CORALean.Global.Float.InverseHyperbolic
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.acosh`

Increasing for `1 ≤ x`, so `acoshDown` at the lower bound and `acoshUp` at the upper one
(`Global/Float/InverseHyperbolic`). CORA throws below `1`; here the domain is a hypothesis of
the theorem.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.acosh (p k : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => acoshDown p k (I.inf i)
  sup := fun i => acoshUp p k (I.sup i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

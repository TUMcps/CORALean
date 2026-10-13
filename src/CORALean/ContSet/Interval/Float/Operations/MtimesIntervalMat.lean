module

public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo

@[expose] public section

/-!
# `Interval.mtimesIntervalMat`, over a floating-point scalar

`Real.Interval.mtimesIntervalMat` rounded, exactly as `matMul` rounds
`Real.Interval.matMul`: a row is the sum over `k` of the corner hull of the
matrix's `(i, k)` interval against the vector's `k`-th one, each hull and the
row sum rounded away from the box.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.mtimesIntervalMat (IM : Interval (Mat 𝕋 m n)) (I : Interval (Vec 𝕋 n)) :
    Interval (Vec 𝕋 m) where
  inf := fun i => sumDown fun k => Interval.mulLo (IM.inf i k) (IM.sup i k) (I.inf k) (I.sup k)
  sup := fun i => sumUp fun k => Interval.mulHi (IM.inf i k) (IM.sup i k) (I.inf k) (I.sup k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

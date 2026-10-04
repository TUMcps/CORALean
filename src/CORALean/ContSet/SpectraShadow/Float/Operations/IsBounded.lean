import CORALean.ContSet.Conversion.Float.SpectraShadow_to_Interval

/-!
# `SpectraShadow.isBounded`, over a floating-point scalar

CORA's `@spectraShadow/isBounded` asks whether every axis support is finite, `2n` semidefinite
programs. Here their dual certificates are the caller's, and the test is whether all of them
check, i.e. whether the certified interval hull exists. Sufficient only: `true` proves the set
bounded, `false` says only that these certificates do not.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.isBounded (S : SpectraShadow 𝕋 n) (Yup Ylo : Fin n → Mat 𝕋 S.k S.k) : Bool :=
  (S.interval Yup Ylo).isSome

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

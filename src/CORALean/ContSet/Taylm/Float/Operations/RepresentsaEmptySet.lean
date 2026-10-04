import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.representsa_emptySet`, over a floating-point scalar

CORA's `representsa(T, 'emptySet')`, answered one-sidedly: `true` only if some component's stored
remainder is crossed, its upper end below its lower end by the strict test `ltStrict`, so the
remainder interval is empty and the range set is `∅`. `false` refutes nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.representsa_emptySet (T : Fin m → Taylm 𝕋 n) : Bool :=
  (List.finRange m).any fun i => ltStrict (T i).remSup (T i).remInf

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

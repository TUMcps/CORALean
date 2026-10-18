module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Taylm

@[expose] public section

/-!
# `Taylm.representsa_emptySet`, over a floating-point scalar

CORA's `representsa(T, 'emptySet')`, answered one-sidedly: `true` only if some component's
remainder with the error box absorbed (`absorbRounding`, the ends rounded outward) is crossed, its
upper end below its lower end by the strict test `ltStrict`, so the exact sum of the remainder and
the box is empty and the range set is `∅`. `false` refutes nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.representsa_emptySet (T : Fin m → Taylm 𝕋 n) : Bool :=
  (List.finRange m).any fun i =>
    ltStrict (T i).absorbRounding.rem.sup (T i).absorbRounding.rem.inf

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

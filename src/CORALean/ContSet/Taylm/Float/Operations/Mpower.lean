module

public import CORALean.ContSet.Taylm.Float.Operations.Mmul
public import CORALean.ContSet.Taylm.Float.Operations.Basic

@[expose] public section

/-!
# `Taylm.mpower`, float

Float analogue of the real `Taylm.mpower`: a positive exponent repeats `mmul`, `0` is the identity
matrix as constant models.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open FloatOps in
def Taylm.mpower {k : ℕ} (A : Fin k → Fin k → Taylm 𝕋 n) :
    ℕ → Fin k → Fin k → Taylm 𝕋 n
  | 0 => fun i j => Taylm.const n (if i = j then one else zero) 0
  | e + 1 => (fun P => Taylm.mmul P A)^[e] A

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

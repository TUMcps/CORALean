import CORALean.ContSet.Taylm.Float.Operations.Times
import CORALean.ContSet.Taylm.Float.Operations.Sum

/-!
# `Taylm.mmul`, float

Float analogue of the real `Taylm.mmul`: CORA's `mtimes` of two arrays of models, entry `(i, j)`
is `Σₖ A i k .* B k j`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.mmul {a b c : ℕ} (A : Fin a → Fin b → Taylm 𝕋 n) (B : Fin b → Fin c → Taylm 𝕋 n) :
    Fin a → Fin c → Taylm 𝕋 n :=
  fun i j => Taylm.sum fun k => (A i k).times (B k j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

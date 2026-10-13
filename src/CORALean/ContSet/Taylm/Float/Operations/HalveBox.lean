import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.halveBox`, over a floating-point scalar

The two halves of a box at coordinate `β`, cut at the midpoint `(l + u) / 2` with the sum rounded
up: the halves cover the box wherever the cut lies.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.halveBox (B : Fin n → 𝕋 × 𝕋) (β : Fin n) : (Fin n → 𝕋 × 𝕋) × (Fin n → 𝕋 × 𝕋) :=
  let m := half (addUp (B β).1 (B β).2)
  (Function.update B β ((B β).1, m), Function.update B β (m, (B β).2))
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

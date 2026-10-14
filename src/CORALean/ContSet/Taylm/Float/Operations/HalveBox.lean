module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Taylm.halveBox`, over a floating-point scalar

The two halves of a box at coordinate `β`, cut at the midpoint `(l + u) / 2` with the sum rounded
up: the halves cover the box wherever the cut lies.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.halveBox (B : Fin n → Interval 𝕋) (β : Fin n) : (Fin n → Interval 𝕋) × (Fin n →
    Interval 𝕋) :=
  let m := half (addUp (B β).inf (B β).sup)
  (Function.update B β ⟨(B β).inf, m⟩, Function.update B β ⟨m, (B β).sup⟩)
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Interval.Float.Operations.EBox

/-!
# `Interval.lift_`, over a floating-point scalar

CORA's `@interval/lift_`: the box placed into the coordinates `proj` of `𝕋ᴺ`, every other
coordinate unbounded. The first `j` with `proj j = i` supplies coordinate `i` (the only one, for
an injective `proj`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


variable {m N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.lift_ (I : Interval (Vec 𝕋 m)) (N : ℕ) (proj : Fin m → Fin N) : Interval.EBox 𝕋 N :=
  let src : Fin N → Option (Fin m) := fun i => (List.finRange m).find? fun j => proj j = i
  ⟨fun i => (src i).map I.inf, fun i => (src i).map I.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

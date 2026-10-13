import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.Interval.Float.Operations.Origin

/-!
# `ConPolyZono.empty`, over a floating-point scalar

No generators and one constraint row that cannot hold: the empty constraint matrix and the
crossed bound `[one, zero]`. The centre is `zero` and the error box the point `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.empty (n : ℕ) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := 0
  h := 0
  q := 0
  m := 1
  s := 0
  c := fun _ => zero
  G := Fin.elim0
  E := fun i => i.elim0
  GI := Fin.elim0
  A := fun _ j => j.elim0
  b := ⟨fun _ => one, fun _ => zero⟩
  EC := fun i => i.elim0
  err := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

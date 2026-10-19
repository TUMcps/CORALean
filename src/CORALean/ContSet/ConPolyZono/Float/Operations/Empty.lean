module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.empty`, over a floating-point scalar

No generators and one constraint row that cannot hold: the empty constraint matrix, whose product
is `0`, held to `one` with no slack. The center is `zero` and the error box the point `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.empty (n : ℕ) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := 0
  h := 0
  qI := 0
  c := fun _ => zero
  G := Fin.elim0
  E := fun i => i.elim0
  GI := Fin.elim0
  cons := ⟨1, 0, fun _ j => j.elim0, fun i => i.elim0, fun _ => one, fun _ => zero, fun _ => .eq,
    Interval.unit 0⟩
  cons_eq _ := rfl
  cons_dom := rfl
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

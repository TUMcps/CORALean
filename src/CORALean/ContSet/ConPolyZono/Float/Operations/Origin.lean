module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.origin`, over a floating-point scalar

The point `0` as a constrained polynomial zonotope with no generators and an empty
constraint system, the center stored as `zero` and the box at zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.origin (n : ℕ) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := 0
  h := 0
  qI := 0
  c := fun _ => zero
  G := Fin.elim0
  E := fun i => i.elim0
  GI := Fin.elim0
  cons := ⟨0, 0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0⟩
  cons_eq i := i.elim0
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

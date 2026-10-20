module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# `HPolytope.eqs`, over a floating-point scalar

CORA's equality constructor. The right-hand side is a point, the slacks zero and the error box
the origin: an equality is kept exact, and an operation that must round one writes the rounding
into its slack (`be_error`), so it stays an equality.

## Inputs
* `Ae` – `q × n` matrix
* `be` – vector of length `q`

## Output
* the polytope with equality rows `Ae x = be`, exact slacks and origin error box
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.eqs (Ae : Mat 𝕋 q n) (be : Vec 𝕋 q) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := 0
  A := fun i => i.elim0
  b := fun i => i.elim0
  me := q
  Ae := Ae
  be := be
  b_error := fun _ => zero
  be_error := fun _ => zero
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

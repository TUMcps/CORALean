module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.Interval.Float.Operations.Origin

@[expose] public section

/-!
# `HPolytope.origin`, over a floating-point scalar

CORA's `polytope.origin(n)` in its halfspace form: no inequalities and the `n` equality rows
`xᵢ = 0`, the identity matrix against the point box `[0, 0]`. The entries are `one` and `zero`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.origin (n : ℕ) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := 0
  A := fun i => i.elim0
  b := fun i => i.elim0
  me := n
  Ae := fun i j => if i = j then one else zero
  be := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

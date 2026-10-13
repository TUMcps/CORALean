module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `Zonotope.entryDeviation`

An upper bound on `|x - e - y|` in one entry, for `y` known only to lie between `lo` and `hi`: the
two signed differences rounded upward, the larger taken. `Zonotope.deviation` is the largest over
the entries.
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

def Zonotope.entryDeviation (x e lo hi : Vec 𝕋 n) (i : Fin n) : 𝕋 :=
  maximum (subUp (subUp (x i) (e i)) (lo i)) (subUp (hi i) (subDown (x i) (e i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

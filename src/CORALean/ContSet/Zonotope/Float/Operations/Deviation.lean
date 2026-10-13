module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `Zonotope.deviation`

An upper bound on the largest entry of `|x - e - y|` for a point `x`, a box corner `e` and a vector
`y` known only to lie between `lo` and `hi`: each entry's two signed differences rounded upward,
the larger taken, then the largest over the entries. What a certified box around `y` is asked to
contain: `x - e` within `B` of `y`.
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

def Zonotope.deviation (x e lo hi : Vec 𝕋 n) : 𝕋 :=
  maximumOver fun i =>
    maximum (subUp (subUp (x i) (e i)) (lo i)) (subUp (hi i) (subDown (x i) (e i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle

@[expose] public section

/-!
# `ZonoBundle.reduce`

To a maximum order: keep the first `o` members, in `Z`'s existing order, and
drop the rest. A bundle denotes an *intersection*, so dropping a member only
enlarges the set — the intersection then runs over fewer factors.

Nothing rounds, and nothing is absorbed: every other float `reduce` in the tree
pays what it drops into an error box, while a bundle just forgets it, for free.
Which members survive is a heuristic with no proof obligation of its own —
`reduce_outer` holds at *any* choice, keeping the first `o` among them.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.reduce (zB : ZonoBundle (Vec 𝕋 n)) (o : ℕ) : ZonoBundle (Vec 𝕋 n) where
  k := min zB.k o
  Z := fun i => zB.Z (Fin.castLE (min_le_left zB.k o) i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

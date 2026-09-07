import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

/-!
# `ZonoBundle.reduce`

To a maximum order: keep the first `o` components, in `Z`'s existing order, and
drop the rest. A bundle denotes an *intersection*, so dropping a component only
enlarges the set — the intersection then runs over fewer factors. That is why
this `reduce`, alone in the tree, carries no error box: every other
representation's `reduce` pays for what it drops by absorbing the discarded
content into what survives, while a bundle just forgets it, for free.

Which components survive is a heuristic with no proof obligation of its own —
`reduce_outer` holds at *any* choice of survivors, keeping the first `o` among
them. A ranking would want to drop whichever component is nearly redundant
given the others, but that is future work, not this change.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.reduce (B : ZonoBundle α) (o : ℕ) : ZonoBundle α where
  k := min B.k o
  Z := fun i => B.Z (Fin.castLE (min_le_left B.k o) i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

@[expose] public section

/-!
# `ZonoBundle.reduce`

To a maximum order: keep the first `o` components, in `Z`'s existing order, and
drop the rest. A bundle denotes an *intersection*, so dropping a component only
enlarges the set — the intersection then runs over fewer factors. That is why
this `reduce`, alone in the tree, carries no error box: every other
representation's `reduce` pays for what it drops by absorbing the discarded
content into what survives, while a bundle just forgets it, for free.

Which components survive is a heuristic with no proof obligation of its own —
the `Reduce` instance's `reduce_outer` (`SetIntersection.memberwise_outer` at the identity)
holds at *any* choice of survivors, keeping the first `o` among them. A ranking would want to
drop whichever component is nearly redundant given the others, but that is future work.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.reduce (zB : ZonoBundle α) (o : ℕ) : ZonoBundle α where
  k := min zB.k o
  Z := fun i => zB.Z (Fin.castLE (min_le_left zB.k o) i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

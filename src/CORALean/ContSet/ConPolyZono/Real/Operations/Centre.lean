import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.centre`

CORA's `@conPolyZono/center`: the field `c`, with no guarantee that it lies in the set.
`centre_mem_construct` says when it does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.centre (cPZ : ConPolyZono α) : α := cPZ.c

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

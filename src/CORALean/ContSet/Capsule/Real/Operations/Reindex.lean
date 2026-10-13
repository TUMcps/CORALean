module

public import CORALean.ContSet.Capsule.Real.Capsule

@[expose] public section

/-!
# `Capsule.reindex`

The coordinates of a capsule read in another order: centre and direction composed with the
relabelling `e`, the radius unchanged. This is CORA's `@capsule/lift_` at the one case it
defines, `length(proj) == N`, where it calls `project` with a permutation; for any other `proj`
CORA throws `notDefined`, new dimensions being unbounded and a capsule always bounded.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.reindex {n m : ℕ} (e : Fin m ≃ Fin n) (C : Capsule n) : Capsule m where
  c := fun i => C.c (e i)
  g := fun i => C.g (e i)
  r := C.r

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

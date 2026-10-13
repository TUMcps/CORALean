import CORALean.ContSet.LevelSet.Real.Operations.Restrict

/-!
# `LevelSet.splitEquality`

CORA's `@levelSet/splitEquality`: the level set is split into the one holding the equality
constraints (`compOp == '=='`) and the one holding the others, each keeping its constraints in
order. CORA returns `[]` for a part with no constraint; here such a part is the level set with no
constraints (`m = 0`), the whole space, which is the neutral element of the intersection the pair
stands for.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `levelSet/splitEquality`: the equality constraints, and the rest. -/
def LevelSet.splitEquality {n : ℕ} (L : LevelSet n) : LevelSet n × LevelSet n :=
  (L.restrict (Finset.univ.filter fun i => L.op i = .eq),
   L.restrict (Finset.univ.filter fun i => L.op i ≠ .eq))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

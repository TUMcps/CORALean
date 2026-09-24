import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

/-!
# What `Reach NeurNetContrSysDT` needs beyond the initial set

`o` and `ho` are `NeurNetContrSysDT.reach`'s own order and its side
condition; `K` is how many steps `reachUnion` takes.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The maximum zonotope order `o` (with `0 < o`) and the step count `K` a
`Reach NeurNetContrSysDT` run is taken at. -/
structure NeurNetContrSysDT.ReachParams where
  o : ℕ
  ho : 0 < o
  K : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

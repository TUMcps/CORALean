import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT

/-!
# What `Reach LinParamSysDT.WithInput` needs beyond the initial set

`o` and `ho` are `LinParamSysDT.reach`'s own order and its side condition;
`K` is how many steps `reachUnion` takes, one `S n` per step from `0` to `K`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The maximum zonotope order `o` (with `0 < o`) and the step count `K` a
`Reach LinParamSysDT.WithInput` run is taken at. -/
structure LinParamSysDT.ReachParams where
  o : ℕ
  ho : 0 < o
  K : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

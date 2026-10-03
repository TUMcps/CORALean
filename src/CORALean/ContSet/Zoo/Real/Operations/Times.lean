import CORALean.ContSet.Zoo.Real.Zoo
import CORALean.ContSet.Taylm.Real.Operations.Times
import CORALean.ContSet.Interval.Real.Operations.Times

/-!
# `Zoo.times`

CORA's `times` of two zoos (`aux_s_times_zz`): `priv_combineZooObjects` keeps the methods both
have, and the members are combined one by one, `Taylm.times` on the Taylor model and
`Interval.times` on the interval. `Option.map₂` is the combination: a member missing on either
side is dropped. CORA's `times.m` (`aux_s_times_zz`) calls `combineZooObjects`, which exists
nowhere (`plus`, `minus` and `mtimes` call `priv_combineZooObjects`), so CORA's elementwise
zoo-by-zoo `.*` fails at run time; this is the operation it intends, which `mtimes` computes for
scalar zoos.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.times (Z₁ Z₂ : Zoo n) : Zoo n :=
  ⟨Option.map₂ Taylm.times Z₁.taylm Z₂.taylm, Option.map₂ Interval.times Z₁.ivl Z₂.ivl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

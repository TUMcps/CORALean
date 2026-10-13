module

public import CORALean.ContSet.Zoo.Real.Zoo
public import CORALean.ContSet.Taylm.Real.Operations.Plus
public import CORALean.ContSet.Interval.Real.Operations.Plus

@[expose] public section

/-!
# `Zoo.plus`

CORA's `plus` of two zoos (`aux_s_plus_zz`): `priv_combineZooObjects` keeps the methods both
have, and the members are combined one by one, `Taylm.plus` on the Taylor model and
`Interval.plus` on the interval. `Option.map₂` is the combination: a member missing on either
side is dropped.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.plus (Z₁ Z₂ : Zoo n) : Zoo n :=
  ⟨Option.map₂ Taylm.plus Z₁.taylm Z₂.taylm, Option.map₂ Interval.plus Z₁.ivl Z₂.ivl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

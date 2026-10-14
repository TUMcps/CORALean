module

public import CORALean.ContSet.Zoo.Real.Zoo
public import CORALean.ContSet.Taylm.Real.Operations.Minus
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Zoo.minus`

CORA's `minus` of two zoos (`aux_s_minus_zz`): `priv_combineZooObjects` keeps the methods both
have, and the members are combined one by one, `Taylm.minus` on the Taylor model and
`Interval.minus` on the interval. `Option.map₂` is the combination: a member missing on either
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

def Zoo.minus (Z₁ Z₂ : Zoo n) : Zoo n :=
  ⟨Option.map₂ Taylm.minus Z₁.taylm Z₂.taylm, Option.map₂ Interval.minus Z₁.ivl Z₂.ivl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

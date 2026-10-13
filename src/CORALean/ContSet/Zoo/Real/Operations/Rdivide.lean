import CORALean.ContSet.Zoo.Real.Zoo
import CORALean.ContSet.Taylm.Real.Operations.Rdivide
import CORALean.ContSet.Interval.Real.Operations.Rdivide

/-!
# `Zoo.rdivide`

CORA's `rdivide` of two zoos (`aux_s_rdivide_zz`), members combined as in `Zoo.plus`. CORA's
code calls `combineZooObjects`, which exists nowhere (the other operations call
`priv_combineZooObjects`), so CORA's zoo-by-zoo `rdivide` (and `mrdivide`) fails at run time;
this is the operation it intends.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zoo.rdivide (Z₁ Z₂ : Zoo n) : Zoo n :=
  ⟨Option.map₂ Taylm.rdivide Z₁.taylm Z₂.taylm, Option.map₂ Interval.rdivide Z₁.ivl Z₂.ivl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

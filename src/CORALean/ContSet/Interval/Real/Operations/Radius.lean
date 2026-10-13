module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.radius`

Half the width: CORA's `rad`, the other half of the centre-deviation split
`Interval.center` gives a box's point. `Theorems/AbsSubCenterLe` is the bound
relating the two.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.radius (I : Interval α) : α := (2:ℝ)⁻¹ • (I.sup - I.inf)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

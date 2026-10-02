import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.max`

CORA's `@interval/max` at two intervals: the coordinatewise larger bound on each side,
`[max inf₁ inf₂, max sup₁ sup₂]`. CORA's one-argument form (`max(I)`, the supremum) is
`Interval.supremum`; a numeric second argument is the degenerate box `Interval.point`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.max (I₁ I₂ : Interval α) : Interval α where
  inf := ofEntry fun i => Max.max (entry I₁.inf i) (entry I₂.inf i)
  sup := ofEntry fun i => Max.max (entry I₁.sup i) (entry I₂.sup i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

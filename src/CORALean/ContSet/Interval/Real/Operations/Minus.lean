import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.minus`

CORA's `@interval/minus`: bounds subtract like-to-like, `inf` from `inf` and
`sup` from `sup` — not `inf` from `sup`. A crossed result denotes `∅`, exactly
as `Interval.construct`'s own docstring says, so no `IsNonempty` hypothesis
belongs here.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.minus (I₁ I₂ : Interval α) : Interval α where
  inf := I₁.inf - I₂.inf
  sup := I₁.sup - I₂.sup

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

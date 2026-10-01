import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.keepMetric`

Girard's metric `‖g‖₁ - ‖g‖∞` on one generator: what boxing it costs, zero on an
axis-aligned generator. The same quantity `Zonotope.girardSplit` ranks by, here
read off a constrained zonotope's generators so that `keepSplit` can break ties
by it.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `‖g‖₁ - ‖g‖∞` of generator `j`; the max folds from `0`, which no `|G j i|` undercuts. -/
noncomputable def ConZonotope.keepMetric (cZ : ConZonotope (Vec ℝ n)) (j : Fin cZ.h) : ℝ :=
  (∑ i, |cZ.G j i|) - Finset.univ.fold max 0 fun i => |cZ.G j i|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

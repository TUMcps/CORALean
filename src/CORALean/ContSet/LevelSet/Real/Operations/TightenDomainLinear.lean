module

public import CORALean.ContSet.LevelSet.Real.Operations.LinearSweep

@[expose] public section

/-!
# `LevelSet.tightenDomainLinear`

CORA's `@levelSet/tightenDomain` with the contractor `'linear'`: `aux_contractorLinear` runs its
sweep `maxIter` times (CORA fixes `maxIter = 8`), the interval gradient being recomputed on the box
each sweep starts from. The equation is the scalar function `f` (CORA requires a single `'=='`
equation), and `grad` is the handle `der.grad`, passed in with the property
`IsGradEnclosure` that the contractor's soundness needs of it. The other contractors
(`'forwardBackward'`, the default, runs `backpropagation` on the symbolic syntax tree; `'taylor'`
and `'split'` use the solved-variable tables) need symbolic data a `LevelSet` does not carry.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def LevelSet.tightenDomainLinear (f : Vec ℝ n → ℝ)
    (grad : Interval (Vec ℝ n) → Interval (Vec ℝ n)) (maxIter : ℕ) (int : Interval (Vec ℝ n)) :
    Interval (Vec ℝ n) :=
  (LevelSet.linearSweep f grad)^[maxIter] int

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

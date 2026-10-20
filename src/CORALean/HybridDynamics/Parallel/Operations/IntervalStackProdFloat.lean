module

public import CORALean.HybridDynamics.Parallel.Operations.Basic
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.stackProd` over floats

CORA's `cartProd_` of boxes at float: the lower bounds stacked and the upper bounds stacked, as
over ℝ. Stacking moves floats without computing on them, so nothing is rounded, and
`Theorems.IntervalStackProdFloatExact` says it is exactly the product of the readings.

## Inputs
* `bs` – boxes of the components

## Output
* stacked product of the float boxes
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {k : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each bound stacks the components' bounds side by side, as `stack` does at ℝ. -/
def Interval.stackProd (bs : ∀ i, Interval (Vec 𝕋 (n i))) : Interval (Vec 𝕋 (∑ i, n i)) where
  inf := fun p => (bs (finSigmaFinEquiv.symm p).1).inf (finSigmaFinEquiv.symm p).2
  sup := fun p => (bs (finSigmaFinEquiv.symm p).1).sup (finSigmaFinEquiv.symm p).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

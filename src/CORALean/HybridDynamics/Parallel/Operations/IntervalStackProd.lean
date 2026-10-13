import CORALean.HybridDynamics.Parallel.Operations.Unstack
import CORALean.ContSet.Interval.Real.Instances

/-!
# `Interval.stackProd`

The Cartesian product of one box per component, as a box of the stacked space: the lower
bounds stacked, the upper bounds stacked. `Theorems.StackProdExact` says it is exactly the
product.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.stackProd (bs : ∀ i, Interval (Vec ℝ (n i))) : Interval (Vec ℝ (∑ i, n i)) :=
  ⟨stack fun i => (bs i).inf, stack fun i => (bs i).sup⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# `HybridDynamics/Parallel/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- ===================================  `Interval.stackProd`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The Cartesian product of one box per component, as a box of the stacked space: the lower
bounds stacked, the upper bounds stacked. `Theorems.StackProdExact` says it is exactly the
product. -/
def Interval.stackProd (bs : ∀ i, Interval (Vec ℝ (n i))) : Interval (Vec ℝ (∑ i, n i)) :=
  ⟨stack fun i => (bs i).inf, stack fun i => (bs i).sup⟩

end CORALean.Real


namespace CORALean

variable {k : ℕ} {n : Fin k → ℕ}


-- ========================================  `unstack`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- The inverse of `stack`: block `i` of a point of the product space. `Theorems.StackUnstack` and
`Theorems.UnstackStack` say the two undo each other. -/
def unstack (z : Vec ℝ (∑ i, n i)) : ∀ i, Vec ℝ (n i) :=
  fun i j => z (finSigmaFinEquiv ⟨i, j⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

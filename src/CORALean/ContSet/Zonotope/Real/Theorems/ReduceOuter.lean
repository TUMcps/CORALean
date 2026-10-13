module

public import CORALean.ContSet.Zonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOuter

@[expose] public section

/-!
# `Zonotope.reduce` over-approximates the zonotope

One line, because `reduce` is Girard's rule under another name. Which rule that
is, is the only content here: `reduceBy_outer` holds at every partition, so any
other choice would discharge this too.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Girard's is the rule `reduce` runs, and this line is the whole of that
choice: any other would discharge it too. -/
theorem Zonotope.reduce_outer (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    Z.construct ⊆ (Z.reduce o).construct :=
  Zonotope.reduceGirard_outer Z o

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

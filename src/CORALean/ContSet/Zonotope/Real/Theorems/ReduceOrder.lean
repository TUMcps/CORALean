module

public import CORALean.ContSet.Zonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOrderLe

@[expose] public section

/-!
# `Zonotope.reduce` bounds the generator count

One line, because `reduce` is Girard's rule under another name, as
`ReduceOuter.lean` already reads it. A reachability bound built on top of this
needs nothing about which rule `reduce` runs, only that some bound holds.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Girard's is the rule `reduce` runs, and this line is the whole of that
choice: any other rule with the same order bound would discharge it too. -/
theorem Zonotope.reduce_order_le (Z : Zonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (Z.reduce o).h ≤ o * n :=
  Zonotope.reduceGirard_order_le Z ho

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.ZonoBundle.Real.Operations.FlowIndex

/-!
# The flow index is a most aligned axis

What `flowIndex` is chosen for: the axis it returns aligns with the flow at least as well as every
other [1, Heuristic flow]. Mathlib's `List.le_of_mem_argmax`, at the list of all axes.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The chosen axis is at least as aligned with `f` as any axis. -/
theorem ZonoBundle.flowIndex_max {f : Vec ℝ n} {i : Fin n} (h : ZonoBundle.flowIndex f = some i)
    (k : Fin n) : |f k| ≤ |f i| :=
  List.le_of_mem_argmax (f := fun i => |f i|) (List.mem_finRange k) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

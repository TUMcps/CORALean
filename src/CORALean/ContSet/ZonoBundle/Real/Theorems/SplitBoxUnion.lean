import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitUnionEnclosingBox
import CORALean.ContSet.ZonoBundle.Real.Operations.DirBox

/-!
# Splitting by the box heuristic is exact

[1, Heuristic box] states no property of `Λ = I` beyond being usable, and its use is
`split_union_enclosingBox` at the identity, invertible with determinant `1`.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The box heuristic's split is exact. -/
theorem ZonoBundle.splitBox_union (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) (j : Fin n) :
    (zB.split (ZonoBundle.dirBox n) (zB.enclosingBox (ZonoBundle.dirBox n) i) j).1.construct
      ∪ (zB.split (ZonoBundle.dirBox n) (zB.enclosingBox (ZonoBundle.dirBox n) i) j).2.construct
      = zB.construct :=
  ZonoBundle.split_union_enclosingBox _ (by simp [ZonoBundle.dirBox]) zB i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

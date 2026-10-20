module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitUnionEnclosingBox
public import CORALean.ContSet.ZonoBundle.Real.Operations.DirFil

@[expose] public section

/-!
# Splitting by the fil heuristic is exact

[1, Heuristic fil] claims no property of the generators it picks. `dirFil` falls back to the
identity where its pick is singular, so its `Λ` is always invertible and the split is exact.

## Inputs
* `zB` – zonotope bundle
* `i` – member index
* `j` – dimension to cut along

## Hypotheses
* none

## Conclusion
* the two halves together are exactly the bundle

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The fil heuristic's split is exact. -/
theorem ZonoBundle.splitFil_union (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) (j : Fin n) :
    (zB.split zB.dirFil (zB.enclosingBox zB.dirFil i) j).fst.construct
      ∪ (zB.split zB.dirFil (zB.enclosingBox zB.dirFil i) j).snd.construct
      = zB.construct := by -- --- PROOF ---
  refine ZonoBundle.split_union_enclosingBox _ ?_ zB i j
  unfold ZonoBundle.dirFil
  dsimp only
  split_ifs with h
  · exact h
  · simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitUnionEnclosingBox
public import CORALean.ContSet.ZonoBundle.Real.Operations.DirBox

@[expose] public section

/-!
# Splitting by the box heuristic is exact

[1, Heuristic box] states no property of `Λ = I` beyond being usable, and its use is
`split_union_enclosingBox` at the identity, invertible with determinant `1`.

## Inputs
* `zB` – zonotope bundle
* `i` – member index
* `j` – dimension to cut along

## Hypotheses
* none

## Conclusion
* the two halves together are exactly the bundle

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.
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

/-- The box heuristic's split is exact. -/
theorem ZonoBundle.splitBox_union (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) (j : Fin n) :
    (zB.split (ZonoBundle.dirBox n) (zB.enclosingBox (ZonoBundle.dirBox n) i) j).fst.construct
      ∪ (zB.split (ZonoBundle.dirBox n) (zB.enclosingBox (ZonoBundle.dirBox n) i) j).snd.construct
      = zB.construct :=
  ZonoBundle.split_union_enclosingBox _ (by simp [ZonoBundle.dirBox]) zB i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

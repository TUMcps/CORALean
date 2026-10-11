import CORALean.ContSet.PolyZonotope.Real.Operations.DecidableExpEdge
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdge
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpWeight
import CORALean.ContSet.PolyZonotope.Real.Operations.GreedyTarget
import CORALean.ContSet.PolyZonotope.Real.Operations.LeafNode
import CORALean.ContSet.PolyZonotope.Real.Operations.PairSplit
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti

/-!
# `PolyZonotope.relaxGreedy`

`[1, Alg. 2]`, the greedy relaxation `relax(PZ, η)` that `[1, Thm. 2]` names: build the graph of
`[1, Def. 5]`, keep each node's lightest outgoing edge, and while edges remain merge a leaf into its
target. One dependent generator is gone per merge, so `fuel = h` suffices and `relaxGreedy` below
takes it.

The printed "Update `G` (remove `(i,j)`, update indices)" is lines 1 and 2 run again on the relaxed
set: the merge keeps the exponent column of `j` and drops that of `i`, a leaf with no incoming edge,
so the remaining nodes keep their lightest edges — up to which of equal weights is taken, the paper
breaking no ties. The merge is `relaxExpMulti`, as in `relaxExpGreedy`.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its
      Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] with at most `fuel` merges. -/
def PolyZonotope.relaxGreedy (η : ℕ) : ℕ → PolyZonotope α → PolyZonotope α
  | 0, PZ => PZ
  | fuel + 1, PZ =>
    let G := PolyZonotope.ExpEdge PZ.E η                                  -- 1: G_{PZ,η}
    let G' := fun i => @PolyZonotope.greedyTarget PZ.h G                  -- 2: greedy(G_{PZ,η})
      (fun i j => PolyZonotope.instDecidableExpEdge PZ.E η i j) (PolyZonotope.expWeight PZ.E) i
    match PolyZonotope.leafNode G' with                                   -- 3: |G.E| > 0
    | none => PZ
    | some (i, j) =>                                                      -- 4, 5: leaf i, (i,j)
      if h2 : 2 ≤ PZ.h then
        let PZ' := PZ.relaxExpMulti (PolyZonotope.pairSplit h2 i j)       -- 6: relax(PZ, i, j)
        PolyZonotope.relaxGreedy η fuel PZ'                               -- 7, 3: update G, loop
      else PZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

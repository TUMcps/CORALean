module

public import CORALean.ContSet.PolyZonotope.Real.Operations.DecidableExpEdge
public import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdge
public import CORALean.ContSet.PolyZonotope.Real.Operations.ExpWeight
public import CORALean.ContSet.PolyZonotope.Real.Operations.GreedyTarget
public import CORALean.ContSet.PolyZonotope.Real.Operations.LeafNode
public import CORALean.ContSet.PolyZonotope.Real.Operations.PairSplit
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti

@[expose] public section

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

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] with at most `fuel` merges. -/
def PolyZonotope.relaxGreedy (η : ℕ) : ℕ → PolyZonotope α → PolyZonotope α
  | 0, PZ => PZ
  | fuel + 1, PZ =>
    -- 1. construct `G_{PZ,η}`, Def. 5
    let G := PolyZonotope.ExpEdge PZ.E η
    -- 2. `G_{PZ,η} ← greedy(G_{PZ,η})`: each node keeps its lightest outgoing edge
    let G' := fun i => @PolyZonotope.greedyTarget PZ.h G
      (fun i j => PolyZonotope.instDecidableExpEdge PZ.E η i j) (PolyZonotope.expWeight PZ.E) i
    -- 3. `while |G_{PZ,η}.E| > 0`; 9. otherwise return `PZ`
    match PolyZonotope.leafNode G' with
    | none => PZ
    -- 4. `i ←` a leaf node of `G_{PZ,η}`; 5. `j ←` the `j ∈ [h]` with `(i, j) ∈ G_{PZ,η}.E`
    | some (i, j) =>
      if h2 : 2 ≤ PZ.h then
        -- 6. `PZ ← relax(PZ, i, j)`, Thm. 1
        let PZ' := PZ.relaxExpMulti (PolyZonotope.pairSplit h2 i j)
        -- 7. update `G_{PZ,η}` (lines 1-2 on the relaxed set) and loop to line 3
        PolyZonotope.relaxGreedy η fuel PZ'
      else PZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

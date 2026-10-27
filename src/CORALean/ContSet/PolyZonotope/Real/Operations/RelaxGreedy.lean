module

public import CORALean.ContSet.PolyZonotope.Real.Operations.DecidableExpEdge
public import CORALean.ContSet.PolyZonotope.Real.Operations.IsExpEdge
public import CORALean.ContSet.PolyZonotope.Real.Operations.ExpWeight
public import CORALean.ContSet.PolyZonotope.Real.Operations.GreedyTarget
public import CORALean.ContSet.PolyZonotope.Real.Operations.LeafNode
public import CORALean.ContSet.PolyZonotope.Real.Operations.PairSplit
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti

@[expose] public section

/-!
# `PolyZonotope.relaxGreedy`

`[1, Alg. 2]`, the greedy relaxation `relax(PZ, η)` that `[1, Thm. 2]` names: build the graph
of `[1, Def. 5]`, keep each node's lightest outgoing edge, and while edges remain merge a leaf
into its target. One dependent generator is gone per merge, so `fuel = h` suffices. The printed
"Update `G`" is lines 1 and 2 run again on the relaxed set: the merge keeps the exponent column
of `j` and drops that of `i`, a leaf, so the remaining nodes keep their lightest edges, up to
which of equal weights is taken. The merge is `relaxExpMulti`, as in `relaxExpGreedy`.

## Inputs
* `η` – exponent threshold

## Output
* function from fuel and set to the greedily relaxed set

## References

* [1] [T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications
      in Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.](../../../../../../references/2024/ladner-aaai-exponent-relaxation.md)
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
    let G := PolyZonotope.IsExpEdge PZ.E η
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

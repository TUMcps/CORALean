import CORALean.ContSet.PolyZonotope.Real.Operations.DecidableExpEdge
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdge
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpWeight
import CORALean.ContSet.PolyZonotope.Real.Operations.PairSplit

/-!
# `PolyZonotope.expGreedySel`

A selection for `relaxExpGreedy` that runs: it searches the graph of
`[1, Def. 5]` for the lightest edge and hands back the split naming its two
generators, the relaxed one first. `[1, Thm. 2]` keeps the lightest outgoing
edge of every node and merges along the forest that leaves; taking the lightest
edge of the whole graph one step at a time is the same rule read one merge at a
time, and either is a heuristic.

It owes no proof. `relaxExpGreedy_outer` holds at every selection, so the
threshold `η`, the weight and the tie-break decide precision and nothing else —
which is also why the graph's decidability is a convenience here rather than
part of any guarantee.

Over a bare exponent matrix, not a set: the edges read nothing else, so one
definition serves both layers. The weight is summed over every factor, which is
the single `eDiff` of `[1, Def. 5]` at a similar pair and the width
`relaxExpMulti` charges at any other.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The lightest edge of the graph, or `none` where it has no edge at all. -/
def PolyZonotope.aux_lightestEdge {p h : ℕ} (E : Fin p → Fin h → ℕ) (η : ℕ) :
    Option (Fin h × Fin h) :=
  ((List.finRange h).flatMap fun i => (List.finRange h).map fun j => (i, j)).foldl
    (fun best ij =>
      if PolyZonotope.ExpEdge E η ij.1 ij.2 then
        match best with
        | none => some ij
        | some b =>
          if PolyZonotope.expWeight E ij.1 ij.2 < PolyZonotope.expWeight E b.1 b.2
            then some ij else some b
      else best)
    none


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The lightest edge of `[1, Def. 5]` as a split `relaxExpGreedy` can merge
along, and `none` once the graph is exhausted. -/
def PolyZonotope.expGreedySel {p h : ℕ} (E : Fin p → Fin h → ℕ) (η : ℕ) :
    Option ((d : ℕ) × (Split (Fin h) into (Fin d) ⊕ (Fin 2))) :=
  if h2 : 2 ≤ h then
    (PolyZonotope.aux_lightestEdge E η).map fun ij =>
      ⟨h - 2, PolyZonotope.pairSplit h2 ij.1 ij.2⟩
  else none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

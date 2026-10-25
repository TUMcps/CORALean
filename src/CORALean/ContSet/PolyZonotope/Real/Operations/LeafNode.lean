module

public import Mathlib.Data.List.Defs
public import Mathlib.Data.Fin.Basic

@[expose] public section

/-!
# `PolyZonotope.leafNode`

Lines 4 and 5 of `[1, Alg. 2]`: a leaf node `i` of the greedy subgraph, one with no incoming edge
and one outgoing edge, and the target `j` of that edge. The subgraph is given by the target
each node keeps. The paper takes any leaf; the least index is taken.

## Inputs
* `h` – number of generators
* `g` – parent map

## Output
* a leaf with its parent, if any

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications in
      Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least leaf `i` of the subgraph `i ↦ g i`, with its target `j`. -/
def PolyZonotope.leafNode {h : ℕ} (g : Fin h → Option (Fin h)) : Option (Fin h × Fin h) :=
  (List.finRange h).findSome? fun i =>
    if (List.finRange h).all (fun i' => g i' != some i) then (g i).map fun j => (i, j) else none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

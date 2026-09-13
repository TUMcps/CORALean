import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti

/-!
# `PolyZonotope.relaxExpGreedy`

The loop of `[1, Thm. 2]`: merge the two dependent generators a selection names, and repeat
until it names none. `[1, Alg. 2]` walks the greedy subgraph of `[1, Def. 5]` — the smallest-weight
outgoing edge of each node, merged along the forest that leaves — one selection among many.

The selection is a parameter and owes no proof. Soundness holds wherever it points, so the
greedy edge, the threshold `η` and the tie-break decide precision alone; `reduceBy` takes its
ranking the same way. `none` is what an exhausted graph returns, and stops the loop.

Steps are `relaxExpMulti` rather than `relaxExp`, which would carry a similarity
hypothesis into every step; at a similar pair the summed width is the single
`eDiff` anyway, so nothing is lost.

Fuel rather than a termination proof: each step drops one dependent generator,
so `pZ.h` steps exhaust the set and the caller says how many to take. The
`O((h+q)hn + h²p)` of `[1, Thm. 2]` is a complexity claim, and belongs to a
`Complexity/` development that does not exist here yet.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Merge at whatever the selection names, at most `n` times. -/
def PolyZonotope.relaxExpGreedy
    (sel : (pZ : PolyZonotope α) →
      Option ((d : ℕ) × (Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)))) :
    ℕ → PolyZonotope α → PolyZonotope α
  | 0, pZ => pZ
  | n + 1, pZ =>
    (sel pZ).elim pZ fun sp => PolyZonotope.relaxExpGreedy sel n (pZ.relaxExpMulti sp.2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

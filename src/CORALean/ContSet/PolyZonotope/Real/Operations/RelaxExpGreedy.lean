module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti

@[expose] public section

/-!
# `PolyZonotope.relaxExpGreedy`

The loop of `[1, Thm. 2]`: merge the two dependent generators a selection names, and repeat
until it names none. `[1, Alg. 2]` walks the greedy subgraph of `[1, Def. 5]` (the smallest
outgoing edge of each node) as one selection among many. The selection is a parameter and owes
no proof: soundness holds wherever it points, so the edge, the threshold `η` and the tie-break
decide precision alone. Steps are `relaxExpMulti`, which carries no similarity hypothesis. Fuel
rather than a termination proof: each step drops one dependent generator, so `pZ.h` steps
exhaust the set. The `O((h+q)hn + h²p)` of `[1, Thm. 2]` is a complexity claim, not made here.

## Inputs
* `sel` – chooser of the next pair of generators

## Output
* function from step count and set to the greedily relaxed set

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications in
      Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

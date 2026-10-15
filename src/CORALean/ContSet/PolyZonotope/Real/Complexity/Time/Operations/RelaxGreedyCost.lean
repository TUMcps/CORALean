module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxGreedy
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxExpMultiCost
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Prod

@[expose] public section

/-!
# `PolyZonotope.relaxGreedyCost`

Asserted, not proved, as the proof of [1, Thm. 2 (complexity)] counts it, for `h` dependent
generators, `q` independent ones, `n` dimensions and `p` factors. The graph of [1, Def. 5] checks
`h²` pairs at `p` factors each; its greedy subgraph is `h²` comparisons; the loop runs at most `h`
times, a node being processed once, each round updating the subgraph in `h` and applying [1, Thm. 1]
in `(h + q) n + h p`. The paper's `(h + q) n` is moving the generators, which the model of
`Global/Cost.lean` charges as writes: a round writes at most `n (1 + 2h + q) + h p` scalars.

`Operations/RelaxGreedy.lean` searches for the leaf in `h²` per round instead of walking the tree,
so its own cost is not this one.

## [1, Thm. 2 (complexity)]: the greedy relaxation is `O((h + q) h n + h² p)`

The proof's arithmetic read off `relaxGreedyCost`: the count is
`2 h² p + 4 h² + n h + 2 h² n + h q n`, at most `8 ((h + q) h n + h² p)` once there is a factor
(`p ≥ 1`). `IsBigO` along all four sizes growing, as the theorem states it.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its
      Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What [1, Alg. 2] costs on `h` dependent and `q` independent generators, `n` dimensions and
`p` factors: the graph, its greedy subgraph, each computed and written, and `h` rounds of an
update and a relaxation writing its result. -/
def PolyZonotope.relaxGreedyCost (h q n p : ℕ) : Cost :=
  ⟨h ^ 2 * p + h ^ 2⟩ + ⟨2 * h ^ 2⟩ + h • (⟨h⟩ + ⟨n * (1 + 2 * h + q) + h * p⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxGreedy
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxExpMulti

/-!
# `PolyZonotope.relaxGreedyCost`

Asserted, not proved, as the proof of [1, Thm. 2 (complexity)] counts it, for `h` dependent
generators, `q` independent ones, `n` dimensions and `p` factors. The graph of [1, Def. 5] checks
`h²` pairs at `p` factors each; its greedy subgraph is `h²` comparisons; the loop runs at most `h`
times, a node being processed once, each round updating the subgraph in `h` and applying [1, Thm. 1]
in `(h + q) n + h p`. The `(h + q) n` is moving the generators, which the model of
`Global/Cost.lean` does not charge; the paper's count is kept.

`Operations/RelaxGreedy.lean` searches for the leaf in `h²` per round instead of walking the tree,
so its own cost is not this one.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What [1, Alg. 2] costs on `h` dependent and `q` independent generators, `n` dimensions and
`p` factors: the graph, its greedy subgraph, and `h` rounds of an update and a relaxation. -/
def PolyZonotope.relaxGreedyCost (h q n p : ℕ) : Cost :=
  ⟨h ^ 2 * p⟩ + ⟨h ^ 2⟩ + h • (⟨h⟩ + ⟨(h + q) * n + h * p⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxExpGreedyCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxGreedy
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Prod

@[expose] public section

/-!
# `PolyZonotope.relaxGreedyCost`

Asserted, not proved, as the proof of [1, Thm. 2 (complexity)] counts it, for `h` dependent
generators, `q` independent ones, `n` dimensions and `p` factors: the graph of [1, Def. 5]
checks `h²` pairs at `p` factors each, its greedy subgraph is `h²` comparisons, and the loop
runs at most `h` times, each round updating in `h` and applying [1, Thm. 1] in `(h + q) n + h p`
(writes: at most `n (1 + 2h + q) + h p` scalars a round). `Operations/RelaxGreedy.lean` differs.
The count `2 h² p + 4 h² + n h + 2 h² n + h q n` is at most `8 ((h + q) h n + h² p)` for `p ≥ 1`.

## Inputs
* `h` – dependent generator count
* `q` – independent generator count
* `n` – dimension
* `p` – number of factors

## Output
* operation count of the greedy relaxation of all pairs

## References

* [1] [T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications
      in Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence,
      2024.](../../../../../../../../references/2024/ladner-aaai-exponent-relaxation.md)
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

module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxWidthMultiCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGreedy
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti

@[expose] public section

/-!
# `PolyZonotope.relaxExpGreedyCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExpGreedy.lean` runs at most
`N` rounds, each asking the selection `sel` for a pair and applying
`relaxExpMulti` to it. The selection is a parameter of the operation, so its
price `csel` is one here: a round costs at most `csel + aux_relaxExpMultiCost n p`,
and the factor count `p` never changes, a merge keeping it. The generator count
falls by one a round and the independent one grows by one, so every round is charged at the
start's `h` dependent and at most `q + N` independent generators.

## Inputs
* `n` – dimension
* `p` – number of factors
* `h` – dependent generator count
* `q` – independent generator count
* `N` – number of relaxation steps
* `csel` – cost of choosing a pair

## Output
* operation count of the greedy relaxation
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What `PolyZonotope.relaxExpMulti` costs at `Vec ℝ n` over `p` factors, keeping `d` dependent
generators with `q` independent ones, and `n * (d + q + 3) + p * (d + 1)` writes for the result. -/
def PolyZonotope.aux_relaxExpMultiCost (n p d q : ℕ) : Cost :=
  ⟨2 * n⟩ + PolyZonotope.relaxWidthMultiCost p + ⟨n * (d + q + 3) + p * (d + 1)⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpGreedy` costs at `Vec ℝ n` and `p` factors over `N` rounds from
`h` dependent and `q` independent generators, the selection costing at most `csel` per round:
each round merges at `h` and `q + N` at most. -/
def PolyZonotope.relaxExpGreedyCost (n p h q N : ℕ) (csel : Cost) : Cost :=
  N • (csel + PolyZonotope.aux_relaxExpMultiCost n p h (q + N))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

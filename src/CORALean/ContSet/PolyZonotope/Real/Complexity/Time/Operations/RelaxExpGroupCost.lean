module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGroup
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxWidthGroupCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpGroupCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExpGroup.lean` merges `k`
generators into one of `d` kept ones. Summing the `k` merged generators is
`n * k` additions and adding that to the target `n`; the `d` kept generators
are each compared against the target index; and each of the `k` merged
generators gets its width over `p` factors and a scaling (`n`).

The result is the center, the `d` kept dependent generators with their exponent columns, and the
`q + k` independent generators: `n * (1 + d + q + k) + p * d` writes.

## Inputs
* `n` – dimension
* `p` – number of factors
* `d` – kept dependent generators
* `q` – independent generator count
* `k` – size of the relaxed group

## Output
* operation count of relaxing a group of generators
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpGroup` costs at `Vec ℝ n`, `p` factors, `d` kept and `k` merged
generators, over `q` independent ones, and `n * (1 + d + q + k) + p * d` writes for the result. -/
def PolyZonotope.relaxExpGroupCost (n p d q k : ℕ) : Cost :=
  ⟨n * (k + 1) + d + k * n⟩ + k • PolyZonotope.relaxWidthGroupCost p +
    ⟨n * (1 + d + q + k) + p * d⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

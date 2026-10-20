module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMid
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxDriftCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpMidCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExpMid.lean` evaluates
`relaxDrift` twice, once for the center's shift (`n` products, `n` additions)
and once for the new generator's radius (`n` products), and adds the two named
generators (`n`).

The result is written once, and the result's `n * (d + q + 3) + p * (d + 1)` entries are written:
the center, the `d + 1`
dependent and `q + 1` independent generators, and the `d + 1` exponent columns.

## Inputs
* `n` – dimension
* `p` – number of factors
* `d` – kept dependent generators
* `q` – independent generator count

## Output
* operation count of one midpoint exponent relaxation
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpMid` costs at `Vec ℝ n` over `p` factors, keeping `d` dependent
generators with `q` independent ones, and `n * (d + q + 3) + p * (d + 1)` writes for the result. -/
def PolyZonotope.relaxExpMidCost (n p d q : ℕ) : Cost :=
  ⟨4 * n⟩ + (2 : ℕ) • PolyZonotope.relaxDriftCost p + ⟨n * (d + q + 3) + p * (d + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

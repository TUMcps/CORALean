module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxWidthMultiCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpMultiCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExpMulti.lean` adds the two
named generators (`n`), sums the widths over the `p` factors and scales the
first generator by the sum (`n`).

The result is written once, and the result's `n * (d + q + 3) + p * (d + 1)` entries are written:
the center, the `d + 1`
dependent and `q + 1` independent generators, and the `d + 1` exponent columns.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpMulti` costs at `Vec ℝ n` over `p` factors, keeping `d` dependent
generators with `q` independent ones, and `n * (d + q + 3) + p * (d + 1)` writes for the result. -/
def PolyZonotope.relaxExpMultiCost (n p d q : ℕ) : Cost :=
  ⟨2 * n⟩ + PolyZonotope.relaxWidthMultiCost p + ⟨n * (d + q + 3) + p * (d + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

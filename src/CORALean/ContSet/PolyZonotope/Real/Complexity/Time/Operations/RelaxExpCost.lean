module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExp
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxWidthCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExp.lean` adds the two
named generators (`n`) and scales the first by `ξ_E` (`relaxWidth`, then `n`
products). The kept generators and exponent columns are copied. The factor
count and the generator count do not enter.

The generators and the exponent columns that are kept are carried into the result, and the result's
`n * (d + q + 3) + p * (d + 1)` entries are written: the center, the `d + 1`
dependent and `q + 1` independent generators, and the `d + 1` exponent columns.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExp` costs at `Vec ℝ n` over `p` factors, keeping `d` dependent
generators with `q` independent ones: `2 * n` for the merged and the new generator,
`relaxWidth`, and `n * (d + q + 3) + p * (d + 1)` writes for the result. -/
def PolyZonotope.relaxExpCost (n p d q : ℕ) : Cost :=
  ⟨2 * n⟩ + PolyZonotope.relaxWidthCost + ⟨n * (d + q + 3) + p * (d + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

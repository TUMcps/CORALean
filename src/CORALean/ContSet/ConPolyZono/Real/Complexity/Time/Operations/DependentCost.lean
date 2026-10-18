module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.DependentCost

@[expose] public section

/-!
# `ConPolyZono.dependentCost`

Asserted, not proved, and no longer zero: `Operations/Dependent.lean` concatenates the generator
blocks, lays `identE` beside the exponent matrix and pads the constraint block with `padE`. Every
entry of any of these is one the operand already held or a literal `0` or `1`, so nothing is
computed, but the result is a new object and each of its entries is a write: those of
`PolyZonotope.dependentCost`, and the constraint block, `A`, `b` and the padded `R`
at `p + qI` rows.

Worth stating exactly as `PolyZonotope.dependentCost` is: `quadMapCost` and `intersectionCost`
pay it before they do anything else.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.dependent` costs at `Vec ℝ n` over `p` factors, `h` dependent and `qI`
independent generators, `m` constraints over `q` constraint generators: the polynomial zonotope's
writes, and `m * q + m + (p + qI) * q` for the constraint block. -/
def ConPolyZono.dependentCost (n p h qI m q : ℕ) : Cost :=
  PolyZonotope.dependentCost n p h qI + ⟨m * q + m + (p + qI) * q⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

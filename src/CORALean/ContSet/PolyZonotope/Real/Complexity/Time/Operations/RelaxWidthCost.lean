module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidth
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.relaxWidthCost`

Asserted, not proved, by reading `Operations/RelaxWidth.lean`: one `eDiffTight` at the exponent
index it names; the factor count does not enter. On the exponents the equality test, the two
parities and their comparison, `min`, `max` and the test `l = 0`, seven operations priced at unit
like the scalar ones the model counts; on the reals `l / h`, `h - l`, `(h - l) / h`,
`l / (h - l)`, the power and the product, six; and one write of the result. CORA's
`minMaxDiffPoly` finds the same value by the roots of a derivative, which the closed form replaces.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxWidth` costs: seven operations on the exponents, six on the reals, and
one write. -/
def PolyZonotope.relaxWidthCost : Cost := ⟨14⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

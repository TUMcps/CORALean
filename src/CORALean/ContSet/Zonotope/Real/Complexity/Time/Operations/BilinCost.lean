module

public import CORALean.ContSet.Zonotope.Real.Operations.Bilin
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.bilinCost`

Asserted, not proved: `Operations/Bilin.lean` applies the bilinear map `f` once
for the center pair, once per generator of `Z₁` against the center of `Z₂`,
once per generator of `Z₂` against the center of `Z₁`, and once per pair of
generators: `1 + h₁ + h₂ + h₁ * h₂` applications. What one costs depends on `f`
and is a parameter, the writes of the vector it returns inside it. `Complexity/Space/` states the
matching size, and the existing
`bilin_h_isBigO` there reads off the same product.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.bilin` costs when one application of `f` costs at most `cf`. -/
def Zonotope.bilinCost (cf : Cost) (h₁ h₂ : ℕ) : Cost := (1 + h₁ + h₂ + h₁ * h₂) • cf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

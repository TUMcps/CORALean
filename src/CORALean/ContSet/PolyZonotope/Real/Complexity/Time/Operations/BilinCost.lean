module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.bilinCost`

Asserted, not proved: `Operations/Bilin.lean` builds one generator per *pair* of extended
columns, `(h₁+1)(h₂+1)` of them, each one application of `f` and an exponent column of `p`
additions, each written (`2 * p` per column); the zero center is `nOut` writes. What one `f`
costs is a parameter, as in `mapCost`: `f` is any bilinear map. `mulCost` is this at the
entrywise product and `quadMapDepCost` at the quadratic form family.

## Inputs
* `cf` – cost of one bilinear form evaluation
* `nOut` – output dimension
* `p` – number of factors
* `h₁` – first dependent generator count
* `h₂` – second dependent generator count

## Output
* operation count of the bilinear image
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.bilin` costs into `Vec ℝ nOut` at a pairing costing at most `cf` per
application, the write of its value included: one `f` and `p` exponent additions, each computed
and written, per pair of extended columns, and `nOut` writes for the zero center. -/
def PolyZonotope.bilinCost (cf : Cost) (nOut p h₁ h₂ : ℕ) : Cost :=
  ((h₁ + 1) * (h₂ + 1)) • (cf + ⟨2 * p⟩) + ⟨nOut⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.bilinCost`

Asserted, not proved, and the count the representation is expensive for:
`Operations/Bilin.lean` builds one generator per *pair* of extended columns,
`(h₁+1)(h₂+1)` of them, each one application of `f` and each carrying an
exponent column that is `p` additions. Nothing else is computed — the
independent block is empty and the center is zero.

What one `f` costs is a parameter, as in `mapCost` and for the same reason: `f`
is any bilinear map, so a caller with no bound on it has no bound here. `mulCost`
is this at the entrywise product and `quadMapDepCost` at the quadratic form
family.

The `p` exponent additions are counted at unit price alongside the scalar work, each with its
write (`2 * p` per column); the zero center is `nOut` writes.
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

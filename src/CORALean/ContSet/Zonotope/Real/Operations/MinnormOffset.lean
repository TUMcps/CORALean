module

public import CORALean.ContSet.Zonotope.Real.Operations.FacetNormal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# `Zonotope.minnormOffset`

One entry of the vector `b` that `minnorm` takes its minimum over: the offset `Δd = Σᵤ |C G⁽ᵘ⁾|`
of `polytope(Z - c)` at a facet normal `C`, where CORA normalizes every row to unit length
(`@zonotope/polytope.m`, l. 119), so here `Δd / ‖C‖₂`. A zero cross product (dependent
generators) is a row CORA removes as `NaN`; the definition there is `0 / 0` and is excluded by
`minnorm`.

Source: [1].

## References

* [1] `contSet/@zonotope/minnorm.m` and `contSet/@zonotope/polytope.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The offset of the unit-length facet row at generator selection `S`: `Σᵤ |Ĉ G⁽ᵘ⁾|` with
`Ĉ = C / ‖C‖₂`. -/
noncomputable def Zonotope.minnormOffset (Z : Zonotope (Vec ℝ (n + 1))) (S : Fin n → Fin Z.h) : ℝ :=
  (∑ υ, |Z.facetNormal S ⬝ᵥ Z.G υ|) / Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

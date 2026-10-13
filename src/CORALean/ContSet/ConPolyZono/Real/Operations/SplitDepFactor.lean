module

public import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset

@[expose] public section

/-!
# `ConPolyZono.splitDepFactor`

CORA's `@conPolyZono/splitDepFactor`: `getSubset` [1, Prop. 14] at factor `r` over `[-1, 0]` and
over `[0, 1]`, the centre and radius of those intervals being `∓1/2` and `1/2`. A pair, as CORA
returns both halves at once. Factor `r` is a position, CORA's `factor` being an identifier.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The halves `αᵣ ∈ [-1, 0]` and `αᵣ ∈ [0, 1]` of `cPZ`, each over the full factor domain. -/
noncomputable def ConPolyZono.splitDepFactor (cPZ : ConPolyZono α) (r : Fin cPZ.p) :
    ConPolyZono α × ConPolyZono α :=
  (cPZ.getSubset r (-(2 : ℝ)⁻¹) (2 : ℝ)⁻¹, cPZ.getSubset r (2 : ℝ)⁻¹ (2 : ℝ)⁻¹)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

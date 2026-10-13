module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCoef
public import CORALean.ContSet.ConPolyZono.Real.Operations.PlusA

@[expose] public section

/-!
# `ConPolyZono.unionUpperA`

The upper half of [1, Thm. 1]'s constraint matrix, its `[Â 0; 0 Ā]`: one row
`α₁α₂ = 1` pinning the two fresh factors to a common sign, and one row carrying
the selector polynomial `unionConCoef` weighs. Block-diagonal, since neither row
reads the other's columns.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two selector rows, side by side. -/
noncomputable def ConPolyZono.unionUpperA (p₁ p₂ : ℕ) :
    Mat ℝ (1 + 1) (1 + (2 + (p₁ + p₁ + (p₂ + p₂ + (p₁ * p₂ + p₁ * p₂))))) :=
  ConPolyZono.plusA (fun _ _ => (1 : ℝ)) (fun _ l => ConPolyZono.unionConCoef p₁ p₂ l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

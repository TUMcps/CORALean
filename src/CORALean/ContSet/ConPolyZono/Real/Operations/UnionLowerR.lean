module

public import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionSel
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `ConPolyZono.unionLowerR`

The monomials the operands' rows are read against, [1, Thm. 1]'s `R_L`: the two
constraint exponent matrices block-diagonally over their own factor blocks,
widened by the two fresh factors, then one column `α₁` for the shared selector
column of `unionLowerA`.

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

/-- Both operands' constraint monomials, and `α₁` for the selector column. -/
def ConPolyZono.unionLowerR {p₁ q₁ p₂ q₂ : ℕ} (R₁ : Fin p₁ → Fin q₁ → ℕ)
    (R₂ : Fin p₂ → Fin q₂ → ℕ) : Fin (p₁ + p₂ + 2) → Fin (q₁ + q₂ + 1) → ℕ :=
  ConPolyZono.appendE (ConPolyZono.padE (PolyZonotope.plusE R₁ R₂) 2)
    (fun k _ => ConPolyZono.unitCol (ConPolyZono.unionSel p₁ p₂) 1 k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

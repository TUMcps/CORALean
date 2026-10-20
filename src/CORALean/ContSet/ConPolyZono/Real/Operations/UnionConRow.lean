module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCoef
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCol
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet

@[expose] public section

/-!
# `ConPolyZono.unionConRow`

The second selector row of [1, Thm. 1]: the selector polynomial `= 0`, its coefficients
`unionConCoef` on the monomials `unionConCol` names, one equation that cuts the factor cube down
to the two branch domains.

## Inputs
* `p₁` – factor count of first operand
* `p₂` – factor count of second operand

## Output
* selector polynomial constraint on the unit box

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The selector polynomial `= 0`, on the union's factors and their unit box. -/
noncomputable def ConPolyZono.unionConRow (p₁ p₂ : ℕ) : PolyLevelSet (p₁ + p₂ + 2) :=
  ⟨1, _, fun _ l => ConPolyZono.unionConCoef p₁ p₂ l, fun k l => ConPolyZono.unionConCol p₁ p₂ l k,
    0, fun _ => .eq, Interval.unit _⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

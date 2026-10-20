module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCol
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet

@[expose] public section

/-!
# `ConPolyZono.unionSelRow`

The first selector row of [1, Thm. 1], `α₁α₂ = 1`, which pins the union's two fresh factors to a
common sign: one equation over the single monomial `α₁α₂`.

## Inputs
* `p₁` – factor count of first operand
* `p₂` – factor count of second operand

## Output
* selector equation on the union's factors

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

/-- `α₁α₂ = 1`, on the union's factors and their unit box. -/
def ConPolyZono.unionSelRow (p₁ p₂ : ℕ) : PolyLevelSet (p₁ + p₂ + 2) :=
  ⟨1, 1, fun _ _ => 1, fun k _ => ConPolyZono.unitCol (ConPolyZono.unionSel p₁ p₂) 1 k
    + ConPolyZono.unitCol (Fin.natAdd (p₁ + p₂) 1) 1 k, fun _ => 1, fun _ => .eq, Interval.unit _⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

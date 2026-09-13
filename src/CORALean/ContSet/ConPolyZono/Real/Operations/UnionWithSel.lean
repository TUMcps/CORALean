import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionSel

/-!
# `ConPolyZono.unionWithSel`

One exponent column multiplied by the branch selector. Half of the columns of
[1, Thm. 1]'s selector constraint are another column times `α₁`, which is how the
constraint reads differently on the two branches at all.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The column `c`, with the selector's exponent raised by one. -/
def ConPolyZono.unionWithSel (p₁ p₂ : ℕ) (c : Fin (p₁ + p₂ + 2) → ℕ) :
    Fin (p₁ + p₂ + 2) → ℕ :=
  fun k => ConPolyZono.unitCol (ConPolyZono.unionSel p₁ p₂) 1 k + c k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

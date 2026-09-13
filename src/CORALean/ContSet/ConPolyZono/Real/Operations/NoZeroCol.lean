import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `ConPolyZono.NoZeroCol`

No column of an exponent matrix is all-zero, so every monomial it names carries a
positive power of some factor and vanishes wherever those factors do.

This is half of [1, Def. 5]'s *regular*. The other half — no two columns alike —
says nothing about what a monomial evaluates to, and no result here asks for it;
[1] bundles the two because `compactGen` and `compactCon` establish both at once.
Stated over a bare exponent matrix rather than over a set, since a constrained
polynomial zonotope carries two of them and `union` needs the property of both.

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

/-- Every column carries a positive exponent somewhere, so none of them is the
constant monomial `1`. -/
def ConPolyZono.NoZeroCol {p h : ℕ} (E : Fin p → Fin h → ℕ) : Prop :=
  ∀ i, ∃ k, E k i ≠ 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Taylm.Real.Taylm

/-!
# `Taylm.bernsteinDegree`

The degree `poly2bernstein` [1] expands at: `n = max(max(E))`, the largest exponent of any variable
in any term, used for every variable (`optBernstein` [2] passes the exponent matrix of the
polynomial). A term list without terms has degree `0`.

## References

* [1] `global/functions/helper/sets/contSet/polyZonotope/poly2bernstein.m`, CORA (Sep. 2025).
      No paper behind the rule was confirmed.
* [2] `contSet/@taylm/optBernstein.m`, CORA (Sep. 2025).
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `max(max(E))`: the largest exponent in any term. -/
def Taylm.bernsteinDegree (T : Taylm n) : ℕ :=
  (T.terms.map fun a => Finset.univ.sup a.2).foldr max 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

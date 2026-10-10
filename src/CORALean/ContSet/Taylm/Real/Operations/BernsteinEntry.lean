import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# `Taylm.bernsteinEntry`

One entry of the matrix `poly2bernstein` [1] multiplies a coefficient column by, once per
variable: `Ux⁻¹ Vx⁻¹ Wx⁻¹` for the domain `[-1, 1]` and degree `N`. The three factors are the
Taylor shift to the lower end `-1` (`Wx`, entries `C(e, i) (-1)^(e - i)`), the scaling by the
width `2` (`Vx`, entries `2ⁱ`), and the change from monomials to Bernstein form (`Ux`, entries
`C(j, i) / C(N, i)`). Entry `(j, e)` is the Bernstein coefficient `j` of the monomial `xᵉ`:
`Σᵢ C(j, i) / C(N, i) · C(e, i) 2ⁱ (-1)^(e - i)`, the sum running to `e`, since `C(j, i) = 0`
for `i > j`.

## References

* [1] `global/functions/helper/sets/contSet/polyZonotope/poly2bernstein.m`, CORA (Sep. 2025).
      No paper behind the rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Bernstein coefficient `j` of the monomial `xᵉ` over `[-1, 1]` at degree `N`: the `(j, e)`
entry of `Ux⁻¹ Vx⁻¹ Wx⁻¹`. -/
noncomputable def Taylm.bernsteinEntry (N e j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (e + 1),
    ((j.choose i : ℝ) / (N.choose i : ℝ)) * ((e.choose i : ℝ) * 2 ^ i * (-1) ^ (e - i))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

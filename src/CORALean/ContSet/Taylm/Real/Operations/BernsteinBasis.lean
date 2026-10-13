import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# `Taylm.bernsteinBasis`

The Bernstein basis polynomial of degree `N` and index `j` on `[0, 1]`:
`B_{j,N}(u) = C(N, j) uʲ (1 - u)^(N - j)`, the basis `poly2bernstein` [1] expands a polynomial in.
Nonnegative on `[0, 1]` and summing to one there, which is why the extreme coefficients bound the
polynomial. Over CORA's normalized box `[-1, 1]` the argument is `u = (x + 1) / 2`.

## References

* [1] `global/functions/helper/sets/contSet/polyZonotope/poly2bernstein.m`, CORA (Sep. 2025).
      No paper behind the rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `B_{j,N}(u) = C(N, j) uʲ (1 - u)^(N - j)`. -/
noncomputable def Taylm.bernsteinBasis (N j : ℕ) (u : ℝ) : ℝ :=
  (N.choose j : ℝ) * u ^ j * (1 - u) ^ (N - j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

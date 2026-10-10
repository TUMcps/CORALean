import CORALean.ContSet.Taylm.Real.Operations.BernsteinBasis
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Bernstein basis is nonnegative on `[0, 1]`

A product of a binomial coefficient and two nonnegative powers [1].

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.bernsteinBasis_nonneg (N j : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ Taylm.bernsteinBasis N j u := by
  have : 0 ≤ 1 - u := by linarith
  unfold Taylm.bernsteinBasis
  positivity

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

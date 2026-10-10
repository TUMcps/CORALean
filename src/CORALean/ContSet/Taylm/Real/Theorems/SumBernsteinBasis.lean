import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import CORALean.ContSet.Taylm.Real.Operations.BernsteinBasis
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The Bernstein basis sums to one

Partition of unity, for every `u`: the binomial theorem at `(u + (1 - u))ᴺ`. With the
nonnegativity on `[0, 1]` it makes a convex combination of the coefficients of a Bernstein
expansion, which [1] uses to bound a polynomial by them.

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

theorem Taylm.sum_bernsteinBasis (N : ℕ) (u : ℝ) :
    ∑ j ∈ Finset.range (N + 1), Taylm.bernsteinBasis N j u = 1 := by -- --- PROOF ---
  have h := add_pow u (1 - u) N
  simp only [add_sub_cancel, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Taylm.bernsteinBasis
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

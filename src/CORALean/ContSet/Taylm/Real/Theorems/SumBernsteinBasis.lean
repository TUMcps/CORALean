module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Intervals
public import CORALean.ContSet.Taylm.Real.Operations.BernsteinBasis
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The Bernstein basis sums to one

Partition of unity, for every `u`: the binomial theorem at `(u + (1 - u))ᴺ`. With the
nonnegativity on `[0, 1]` it makes a convex combination of the coefficients of a Bernstein
expansion, which [1] uses to bound a polynomial by them.

## Inputs
* `N` – degree
* `u` – point of the unit interval

## Hypotheses
* none

## Conclusion
* the Bernstein basis polynomials sum to one

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sum_bernsteinBasis (N : ℕ) (u : ℝ) : -- --- CONCL ---
    ∑ j ∈ Finset.range (N + 1), Taylm.bernsteinBasis N j u = 1 := by -- --- PROOF ---
  have h := add_pow u (1 - u) N
  simp only [add_sub_cancel, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Taylm.bernsteinBasis
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

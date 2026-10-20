module

public import CORALean.ContSet.Taylm.Real.Operations.BernsteinBasis
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The Bernstein basis is nonnegative on `[0, 1]`

A product of a binomial coefficient and two nonnegative powers [1].

## Inputs
* `N` – degree
* `j` – index
* `u` – point of the unit interval

## Hypotheses
* `h0` – argument is at least zero
* `h1` – argument is at most one

## Conclusion
* the basis value is nonnegative

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

theorem Taylm.bernsteinBasis_nonneg (N j : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ Taylm.bernsteinBasis N j u := by
  have : 0 ≤ 1 - u := by linarith
  unfold Taylm.bernsteinBasis
  positivity

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

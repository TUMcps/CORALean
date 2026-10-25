module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas

@[expose] public section

/-!
# Setting one entry is adding a multiple of a basis vector

The step behind the single-entry derivatives of [1, Def. 3]: `x` with its `j`-th entry set to `t`
is `x + (t - x(j)) e_j`, a point on a line through `x`, so that a derivative along the entry is a
derivative along a line.

## Inputs
* `x` – vector
* `j` – coordinate
* `t` – new value

## Hypotheses
* none

## Conclusion
* updating a coordinate adds a multiple of the unit vector

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem update_eq_add_single (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    Function.update x j t = x + (t - x j) • (Pi.single j 1 : Fin n → ℝ) := by
  funext k
  by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

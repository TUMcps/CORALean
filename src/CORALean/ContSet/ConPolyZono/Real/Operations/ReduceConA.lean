module

public import CORALean.Global.DropIdx
public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `ConPolyZono.reduceConA`

The constraint matrix of [1, Prop. 13]: row `r` and column `t` struck out, and
every remaining entry corrected by `A(r,i) A(j,t) / A(r,t)`.

The correction is rank one — column `t` of the surviving rows times row `r` of
the surviving columns — and it is what makes the eliminated row's substitution
hold in the rows that stay: each of them had a multiple of `A(j,t)` riding on
the monomial `r` solves for, and this subtracts exactly that.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `r` and column `t` gone, the rest corrected by a rank-one term. -/
noncomputable def ConPolyZono.reduceConA {m s : ℕ} (A : Mat ℝ m s) (r : Fin m) (t : Fin s) :
    Mat ℝ (m - 1) (s - 1) :=
  Matrix.of fun j i => A (dropIdx r j) (dropIdx t i)
    - A r (dropIdx t i) * A (dropIdx r j) t / A r t

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.Global.DropIdx

@[expose] public section

/-!
# `PolyLevelSet.eliminate`

Row `r` solved for its monomial `t` and that monomial substituted into the rows that stay, as
[1, Prop. 13] does with a constraint: row `r` and monomial `t` struck out, every surviving
coefficient corrected by `A(r,i) A(j,t) / A(r,t)` and every surviving right-hand side shifted by
`b(r) A(j,t) / A(r,t)`. The correction is rank one, and it is what makes the eliminated row's
substitution hold in the rows that stay: each of them had a multiple of `A(j,t)` riding on the
monomial `r` solves for, and this subtracts exactly that. Where row `r` is an equation that holds,
every surviving row takes its old value (`mem_eliminate_of_mem`).

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `r` and monomial `t` gone, the rest corrected by the substitution row `r` gives. -/
noncomputable def PolyLevelSet.eliminate (P : PolyLevelSet n) (r : Fin P.m) (t : Fin P.q) :
    PolyLevelSet n where
  m := P.m - 1
  q := P.q - 1
  A := Matrix.of fun j i => P.A (dropIdx r j) (dropIdx t i)
    - P.A r (dropIdx t i) * P.A (dropIdx r j) t / P.A r t
  R k i := P.R k (dropIdx t i)
  b j := P.b (dropIdx r j) - P.b r * P.A (dropIdx r j) t / P.A r t
  op j := P.op (dropIdx r j)
  dom := P.dom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

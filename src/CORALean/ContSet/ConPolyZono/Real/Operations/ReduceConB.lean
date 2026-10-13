import CORALean.ContSet.Interval.Real.Interval
import CORALean.Global.DropIdx

/-!
# `ConPolyZono.reduceConB`

The constraint vector of [1, Prop. 13]: entry `r` struck out, and every
surviving entry shifted by `b(r) A(j,t) / A(r,t)` — the constant the eliminated
row contributes once its monomial is substituted away.

`b` is an `Interval` here where [1, Def. 5] has a vector, and the row being
eliminated is the one place that matters: a row read as `A μ(α) ∈ b(r)` does not
determine the monomial it is solved for, only pin it to an interval, so the
value read off is `inf` and `reduceCon_outer` carries the hypothesis saying that
row is a point. Every other row keeps its width, shifted by a constant.

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

/-- Entry `r` gone, the rest shifted by what the eliminated row leaves behind. -/
noncomputable def ConPolyZono.reduceConB {m s : ℕ} (A : Mat ℝ m s) (b : Interval (Vec ℝ m))
    (r : Fin m) (t : Fin s) : Interval (Vec ℝ (m - 1)) where
  inf := fun j => b.inf (dropIdx r j) - b.inf r * A (dropIdx r j) t / A r t
  sup := fun j => b.sup (dropIdx r j) - b.inf r * A (dropIdx r j) t / A r t

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

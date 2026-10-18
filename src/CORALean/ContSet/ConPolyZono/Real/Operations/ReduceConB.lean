module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Global.DropIdx

@[expose] public section

/-!
# `ConPolyZono.reduceConB`

The constraint vector of [1, Prop. 13]: entry `r` struck out, and every
surviving entry shifted by `b(r) A(j,t) / A(r,t)` — the constant the eliminated
row contributes once its monomial is substituted away.


## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Entry `r` gone, the rest shifted by what the eliminated row leaves behind. -/
noncomputable def ConPolyZono.reduceConB {m q : ℕ} (A : Mat ℝ m q) (b : Vec ℝ m)
    (r : Fin m) (t : Fin q) : Vec ℝ (m - 1) :=
  fun j => b (dropIdx r j) - b r * A (dropIdx r j) t / A r t

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

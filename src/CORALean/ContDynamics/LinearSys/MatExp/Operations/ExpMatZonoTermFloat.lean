import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
import CORALean.ContSet.MatZonotope.Float.Operations.MatPow
import CORALean.ContSet.MatZonotope.Float.Operations.Smul

/-!
# `MatExp.expMatZonoTerm`, over a floating-point scalar

`Real.MatExp.expMatZonoTerm` rounded: the matrix zonotope's `i`-th power scaled by
`1/i!`, which no float holds exactly, so by `invFactorialBounds i` as an interval, the
same handle `expIntervalTaylor` uses.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Order `i` of [1, Sec. 3.3.2]'s series: the `i`-th power, scaled by `[1/i!]`. -/
def MatExp.expMatZonoTerm (M : MatZonotope 𝕋 n n) (i : ℕ) : MatZonotope 𝕋 n n :=
  MatZonotope.smul (MatExp.invFactorialBounds i).1 (MatExp.invFactorialBounds i).2 (M.matPow i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorTailFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalWFloat

@[expose] public section

/-!
# Interval matrices: the Taylor truncation with an exact second order, in floats

`expIntervalTaylorExact`: the truncation of [1, Thm. 3.2], `Real.MatExp.expIntervalTaylorExact`
rounded: the identity and `W(t)` through `expIntervalW`, the rest by interval arithmetic at
`[t] A`. The time is a float `t`, scaling by the degenerate bracket `[t, t]`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The truncation of [1, Thm. 3.2]: the identity and `W(t)` exactly, the rest by interval
arithmetic. -/
def MatExp.expIntervalTaylorExact (A : Interval (Mat 𝕋 n n)) (t : 𝕋) (κ : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let W := (MatExp.expIntervalW A t).materialiseMat                 -- W(t)
  let T := MatExp.expIntervalTaylorTail (Interval.smul t t A) κ     -- orders 3 … κ of t A
  (Interval.matPlus (Interval.matPlus (Interval.point (diagonalBlock fun _ => one)) W) T)
    |>.materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

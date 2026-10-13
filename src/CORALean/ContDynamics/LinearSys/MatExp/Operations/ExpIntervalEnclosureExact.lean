module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorExact
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContSet.Interval.Real.Operations.AbsMax
public import CORALean.ContSet.Interval.Real.Operations.Smul

@[expose] public section

/-!
# Interval matrices: the exponential enclosed with an exact second order

`expIntervalEnclosureExact`: `e^{At}_[κ]` of [1, Thm. 3.2]: the truncation
`expIntervalTaylorExact` widened by `E(t)`, the tail bound taken at `t • A`'s dominating
matrix as `expIntervalEnclosure` takes it, so the two enclosures differ only where they
should. The identity costs nothing, `W(t)` is `expIntervalW` and therefore exact, and only
the orders from three on are left to ordinary interval arithmetic — which is what makes this
sharper than `expIntervalEnclosure`, where every order is.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `e^{At}_[κ]` of [1, Thm. 3.2]: that truncation widened by `E(t)`, the tail
bound taken at `t • A`'s dominating matrix as `expIntervalEnclosure` takes it. -/
noncomputable def MatExp.expIntervalEnclosureExact (A : Interval (Mat ℝ n n)) (t : ℝ)
    (κ : ℕ) : Interval (Mat ℝ n n) where
  inf := fun i j => (MatExp.expIntervalTaylorExact A t κ).inf i j
    - MatExp.expRemainderBound (Interval.smul t A).absMax κ
  sup := fun i j => (MatExp.expIntervalTaylorExact A t κ).sup i j
    + MatExp.expRemainderBound (Interval.smul t A).absMax κ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

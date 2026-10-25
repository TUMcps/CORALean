module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorExact
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContSet.Interval.Real.Operations.AbsMax

@[expose] public section

/-!
# Interval matrices: the exponential enclosed with an exact second order

`expIntervalEnclosureExact`: `⌈e^{At}_κ⌉` of [1, Thm. 1]: the truncation
`expIntervalTaylorExact` widened by `E(t)`, the tail bound taken at `t • A`'s dominating
matrix as `expIntervalEnclosure` takes it, so the two enclosures differ only where they
should. The identity costs nothing, `W(t)` is `expIntervalW` and therefore exact, and only
the orders from three on are left to ordinary interval arithmetic — which is what makes this
sharper than `expIntervalEnclosure`, where every order is.

## Inputs
* `A` – interval matrix
* `t` – time
* `κ` – Taylor order

## Output
* interval matrix enclosing the exponential with an exact second order

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Sonnet 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⌈e^{At}_κ⌉` of [1, Thm. 1]: that truncation widened by `E(t)`, the tail
bound taken at `t • A`'s dominating matrix as `expIntervalEnclosure` takes it. -/
noncomputable def MatExp.expIntervalEnclosureExact (A : Interval (Mat ℝ n n)) (t : ℝ)
    (κ : ℕ) : Interval (Mat ℝ n n) where
  inf := fun i j => (MatExp.expIntervalTaylorExact A t κ).inf i j
    - MatExp.expRemainderBound (Interval.smul t A).absMax κ
  sup := fun i j => (MatExp.expIntervalTaylorExact A t κ).sup i j
    + MatExp.expRemainderBound (Interval.smul t A).absMax κ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

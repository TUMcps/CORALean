import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContDynamics.LinearSys.MatExp.ExactSecondOrder
import CORALean.ContSet.Interval.Real.Operations.AbsMax
import CORALean.ContSet.Interval.Real.Operations.MatPow
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Operations.Smul

/-!
# Interval matrices: the exponential enclosed with an exact second order

[1, Thm. 3.2]: `e^{At}_[κ] = I + W(t) + ∑_{i=3}^{κ} (1/i!) (A t)^i + E(t)`. The
identity costs nothing, `W(t)` is `expIntervalW` and therefore exact, and only
the orders from three on are left to ordinary interval arithmetic — which is
what makes this sharper than `expIntervalEnclosure`, where every order is.

`expIntervalTaylorTail` holds those orders, and is `point 0` below order three
rather than undefined, so `κ < 3` is the truncation `I + W(t)` and not a
special case. Its `(A t)^i` is `matPow`, right-associated: [1] writes the power
with no association, and interval matrix multiplication has none.

The remainder is the one `expIntervalEnclosure` uses at the same interval
matrix `t • A`, so the two enclosures differ only where they should.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- Orders `3 … κ` of the Taylor series at an interval matrix, by ordinary
interval arithmetic. Below order three there are none. -/
noncomputable def MatExp.expIntervalTaylorTail (B : Interval (Mat ℝ n n)) :
    ℕ → Interval (Mat ℝ n n)
  | 0 => Interval.point 0
  | 1 => Interval.point 0
  | 2 => Interval.point 0
  | k + 3 => Interval.plus
      (Interval.smul ((Nat.factorial (k + 3) : ℝ)⁻¹) (Interval.matPow B (k + 3)))
      (MatExp.expIntervalTaylorTail B (k + 2))

/-- The truncation of [1, Thm. 3.2]: the identity and `W(t)` exactly, the rest
by interval arithmetic. -/
noncomputable def MatExp.expIntervalTaylorExact (A : Interval (Mat ℝ n n)) (t : ℝ)
    (κ : ℕ) : Interval (Mat ℝ n n) :=
  Interval.plus (Interval.plus (Interval.point 1) (MatExp.expIntervalW A t))
    (MatExp.expIntervalTaylorTail (Interval.smul t A) κ)


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

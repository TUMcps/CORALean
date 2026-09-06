import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContSet.Interval.Real.Operations.AbsMax
import CORALean.ContSet.Interval.Real.Operations.MatPow
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.Smul

/-!
# Interval matrices: enclosing the exponential of an interval matrix

[1, Sec. 3.3.1]: `expTaylor`/`expEnclosure` at one matrix, widened to bound
every matrix a whole box could hold. Not exact: `matPow A k` admits products of
*different* members of `A` at different factors, so the Taylor terms are
bounded independently of each other and of any one `M` they might come from —
ordinary interval-arithmetic dependency loss, and why [1, Sec. 3.3.2] moves on
to matrix zonotopes instead.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- The Taylor truncation as an interval matrix, `i = 0 … η` matching
`MatExp.expTaylor`'s `Finset.range (η + 1)` exactly. -/
noncomputable def MatExp.expIntervalTaylor (A : Interval (Mat ℝ n n)) :
    ℕ → Interval (Mat ℝ n n)
  | 0 => Interval.smul ((Nat.factorial 0 : ℝ)⁻¹) (Interval.matPow A 0)
  | k + 1 => Interval.plus
      (Interval.smul ((Nat.factorial (k + 1) : ℝ)⁻¹) (Interval.matPow A (k + 1)))
      (MatExp.expIntervalTaylor A k)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Taylor box widened by the remainder bound taken at `A.absMax`, so the
tail bound is checkable from the interval matrix alone rather than at whichever
member of it a step turns out to hold. -/
noncomputable def MatExp.expIntervalEnclosure (A : Interval (Mat ℝ n n)) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun i j => (MatExp.expIntervalTaylor A η).inf i j
    - MatExp.expRemainderBound A.absMax η
  sup := fun i j => (MatExp.expIntervalTaylor A η).sup i j
    + MatExp.expRemainderBound A.absMax η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

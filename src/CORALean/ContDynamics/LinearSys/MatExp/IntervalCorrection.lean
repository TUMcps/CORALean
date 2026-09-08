import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContSet.Interval.Real.Operations.AbsMax
import CORALean.ContSet.Interval.Real.Operations.MatPow
import CORALean.ContSet.Interval.Real.Operations.Smul

/-!
# Interval matrices: the correction matrix and the input remainder of a box

[1, Sec. 3.3.1] applied to the two objects a continuous-time step is built from
rather than to the exponential alone: `correctionMatrix` and `inputRemainder`
at an interval matrix, so a system whose matrix is a set has a step to take.

The finite orders are CORA's `priv_tie` of `@linParamSys`: the interval
`[corrCoeff i, 0]` times the box `matPow A i`, one order at a time. Here the
scalar factor is multiplied in by `Interval.smul` and the `min`/`max` against
zero is what the second endpoint of `[corrCoeff i, 0]` contributes, so an entry
is the same product of two intervals CORA takes.

`matPow` is where the dependency loss is, as in `IntervalEnclosures`: it admits
products of different members at different factors.

The tail is taken at a dominating matrix for the reason `ExpIntervalEnclosure`
gives — checkable from the box alone, before a member is fixed — and at `r • A`,
so one condition serves this and the exponential enclosure of a step at once.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- What order `i` contributes to the correction over a whole box: `corrTerm`'s
scalar factor against the box the `i`-th power lies in. -/
noncomputable def MatExp.intervalCorrTerm (A : Interval (Mat ℝ n n)) (r : ℝ) (i : ℕ) :
    Interval (Mat ℝ n n) :=
  Interval.smul (MatExp.corrCoeff i * r ^ i * ((Nat.factorial i : ℝ))⁻¹) (A.matPow i)

/-- The `E(r)·r` of [1] over a whole box: one width for every entry and every
member, the tail bound being on a norm. -/
noncomputable def MatExp.intervalInputRemainder (A : Interval (Mat ℝ n n)) (r : ℝ)
    (η : ℕ) : Interval (Mat ℝ n n) where
  inf := fun _ _ => -(r * MatExp.expRemainderBound (Interval.smul r A).absMax η)
  sup := fun _ _ => r * MatExp.expRemainderBound (Interval.smul r A).absMax η


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of [1] over a whole box: orders `2` through `η` from
`intervalCorrTerm`, everything past `η` in the tail bound at `r • A`, and
indexed from `2` exactly as the point case is. -/
noncomputable def MatExp.intervalCorrectionMatrix (A : Interval (Mat ℝ n n)) (r : ℝ)
    (η : ℕ) : Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range (η - 1),
      min ((MatExp.intervalCorrTerm A r (i + 2)).inf j k) 0)
    - MatExp.expRemainderBound (Interval.smul r A).absMax η
  sup := fun j k => (∑ i ∈ Finset.range (η - 1),
      max ((MatExp.intervalCorrTerm A r (i + 2)).sup j k) 0)
    + MatExp.expRemainderBound (Interval.smul r A).absMax η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

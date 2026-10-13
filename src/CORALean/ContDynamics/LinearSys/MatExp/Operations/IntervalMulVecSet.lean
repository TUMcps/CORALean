import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Data.Matrix.Mul

/-!
# An interval matrix acting on a vector set

`intervalMulVecSet`: the set an interval matrix entrywise within `|E|` of `0` can map `S` to —
[1]'s `[-E(Δt,η),E(Δt,η)]` acting on a vector set.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set an interval matrix entrywise within `|E|` of `0` can map `S` to — [1]'s
`[-E(Δt,η),E(Δt,η)]` acting on a vector set. -/
noncomputable def MatExp.intervalMulVecSet (E : Mat ℝ n n) (S : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  {y | ∃ M : Mat ℝ n n, (∀ i j, |M i j| ≤ |E i j|) ∧ y ∈ (fun x => M.mulVec x) '' S}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

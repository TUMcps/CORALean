import CORALean.Global.Mathlib

/-!
# Bisection for `estimateGain`

`estimateGainSearch`: [1]'s bisection, halve the bracket toward where `g` crosses `target`,
`fuel` times, and hand back the last midpoint.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Halve the bracket toward where `g` crosses `target`, `fuel` times, and hand
back the last midpoint. -/
noncomputable def estimateGainSearch (le : ℝ → ℝ → Bool) (g : ℝ → ℝ) (target : ℝ) :
    ℝ → ℝ → ℕ → ℝ
  | lo, hi, 0 => (lo + hi) / 2
  | lo, hi, k + 1 =>
    let mid := (lo + hi) / 2
    if le (g mid) target then estimateGainSearch le g target mid hi k
    else estimateGainSearch le g target lo mid k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

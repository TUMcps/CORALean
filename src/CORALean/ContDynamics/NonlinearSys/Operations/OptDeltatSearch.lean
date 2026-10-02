import Mathlib.Data.Real.Basic

/-!
# Eq. (58)'s evaluation: increase `λ'` while the estimate falls

`optDeltatSearch`: increase `λ'` while the estimate keeps falling, and stop
at the first increase — [1]'s own evaluation of eq. (58). No `Nat.find` and
no `Classical.choose`, every decision going through the caller's `le`, and
`fuel` bounding a loop with no stated iteration count.

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

/-- Increase `λ'` while the estimate keeps falling, and stop at the first
increase — [1]'s own evaluation of eq. (58). -/
noncomputable def optDeltatSearch (le : ℝ → ℝ → Bool) (cost : ℕ → ℝ) : ℕ → ℕ → ℕ
  | s, 0 => s
  | s, k + 1 => if le (cost (s + 1)) (cost s) then optDeltatSearch le cost (s + 1) k else s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

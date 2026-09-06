import CORALean.ContSet.Interval.Real.Operations.MatPow
import CORALean.ContSet.Interval.Real.Theorems.MatMulOuter
import CORALean.ContSet.Interval.Real.Theorems.MemPoint

/-!
# `Interval.matPow` encloses every power of a matrix in the box

Induction on `k`, unfolding `matPow`'s right recursion with `pow_succ'`
(`M ^ (k + 1) = M * M ^ k`, the *left*-multiplying one, matching how `matPow`
recurses) against `matMul_outer` and the induction hypothesis; the base case is
`mem_point` at `1`.

Holds for one fixed `M` at every power, but the interval arithmetic does not
know that: `matPow A 2` also contains `M * N` for different members `M`, `N` of
`A`. That dependency loss grows with `k`, and is why Althoff §3.3.2 moves on to
matrix zonotopes instead.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.matPow_outer (A : Interval (Mat ℝ n n)) {M : Mat ℝ n n}
    (hM : M ∈ A.construct) (k : ℕ) : M ^ k ∈ (Interval.matPow A k).construct := by
  induction k with
  | zero => rw [pow_zero]; exact Interval.mem_point 1
  | succ k ih => rw [pow_succ']; exact Interval.matMul_outer A (A.matPow k) hM ih

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

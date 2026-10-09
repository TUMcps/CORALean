import CORALean.Global.Float.FloatOps

/-!
# Eq. (58)'s evaluation, in floats

`optDeltatSearch` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no
soundness statement reads it, so every rounding is upward and no theorem is owed. What a run
guarantees holds for whatever this returns. See [1].

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Increase `λ'` while the estimate keeps falling, and stop at the first
increase — [1]'s own evaluation of eq. (58). -/
def optDeltatSearchFloat (cost : ℕ → 𝕋) : ℕ → ℕ → ℕ
  | s, 0 => s
  | s, k + 1 => if le (cost (s + 1)) (cost s) then optDeltatSearchFloat cost (s + 1) k else s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

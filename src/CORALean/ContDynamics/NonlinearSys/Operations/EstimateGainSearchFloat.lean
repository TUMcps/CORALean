import CORALean.Global.Float.FloatOps

/-!
# Bisection for `estimateGain`, in floats

`estimateGainSearch` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no
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

/-- Halve the bracket toward where `g` crosses `target`, `fuel` times, and hand
back the last midpoint. -/
def estimateGainSearchFloat (g : 𝕋 → 𝕋) (target : 𝕋) : 𝕋 → 𝕋 → ℕ → 𝕋
  | lo, hi, 0 => half (addUp lo hi)
  | lo, hi, k + 1 =>
    let mid := half (addUp lo hi)
    if le (g mid) target then estimateGainSearchFloat g target mid hi k
    else estimateGainSearchFloat g target lo mid k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

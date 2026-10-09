import CORALean.Global.Float.FloatOps
import CORALean.Global.Tensor

/-!
# `gainMax`: the gain of a step size, in floats

`gainMax` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no soundness
statement reads it, so every rounding is upward and no theorem is owed. What a run guarantees
holds for whatever this returns. See [1].

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

/-- `φ(Δt)` of eq. (25): the worst dimension's ratio of the two error widths. -/
def gainMaxFloat {n : ℕ} (d dδ : Fin n → 𝕋) : 𝕋 :=
  (List.finRange n).foldl
    (fun φ i => if le φ (divUp (dδ i) (d i)) then divUp (dδ i) (d i) else φ) zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

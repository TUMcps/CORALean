import CORALean.Global.Float.FloatOps
import CORALean.Global.Tensor

/-!
# `tuneAbstrOrder`: the abstraction order for the next step, in floats

`tuneAbstrOrder` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no
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

/-- [1, Alg. 2] line 13: the abstraction order of the next step, from the two
error radii of eq. (46) and the two diameter vectors of eq. (47). -/
def tuneAbstrOrderFloat {n : ℕ} (ζK φstar rabs rabsLast : 𝕋) (d1 d2 : Fin n → 𝕋) (κ : ℕ) : ℕ :=
  if le (absolute (divUp (mulUp φstar rabs) rabsLast)) (subDown one ζK)
    then κ                                                       -- 46. too close to re-tune
  else if ∀ i : Fin n, le (d1 i) zero = true ∨ le ζK (divUp (d2 i) (d1 i)) = true
    then 1                                                       -- 47. quadratic wins too little
    else 2                                                       -- 47. it is worth its cost

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

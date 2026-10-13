import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# One modified Gram–Schmidt sweep

Lines 4–7 of [1, Alg. 1]: for `j = 1, …, k`, `h_{j,k} = w* v(j)` and `w := w - h_{j,k} v(j)`,
each coefficient taken against the `w` the previous ones have already reduced — the
modified, stabilized process [1] names, not classical Gram–Schmidt. Real vectors, so `w*` is
the transpose. Returns the reduced `w` and the coefficients, `v(j)` stored at index `j - 1`.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Krylov.gramSchmidtStep (w : Vec ℝ n) (V : ℕ → Vec ℝ n) : ℕ → Vec ℝ n × (ℕ → ℝ)
  | 0 => (w, fun _ => 0)
  | j + 1 =>
    let prev := Krylov.gramSchmidtStep w V j
    let h := prev.1 ⬝ᵥ V j
    (prev.1 - h • V j, Function.update prev.2 j h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

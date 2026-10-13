import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# The augmented matrix of a constant input

[1, Lemma IV.1]'s `C = [A u; 0₁ₓₙ 0]`: the input `u` appended as a last column and a zero row
below, so that `x̃ = [x_p; x̌]` with `x̃(0) = [0ₙ; 1]` solves `ẋ_p = A x_p + u`, `x̌̇ = 0`. The last
index of `Fin (n + 1)` is the appended one.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[A u; 0 0]`, rows and columns `0, …, n - 1` from `A`, the last column `u`, the last row `0`. -/
def Krylov.augment (A : Mat ℝ n n) (u : Vec ℝ n) : Mat ℝ (n + 1) (n + 1) :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => ℝ) 0
      (fun i' => Fin.lastCases (motive := fun _ => ℝ) (u i') (fun j' => A i' j') j) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

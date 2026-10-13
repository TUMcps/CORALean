import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# The parameter set before the next measurement, by the paper's recursion

[1, Sec. 3]: "`FSS_{k+1} = (FSS_k ∩ F_dk) ⊕ γ Bⁿ`", started from `Θ₀`, with the strip `F_dk = {θ |
-σ ≤ r_kᵀθ - y_k ≤ σ}` of the `k`-th measurement. This is the set of parameters at time `k + 1`
that agree with the first `k` measurements, before the `(k+1)`-th is used, which is why it is not
[1, Def. 1]'s set `feasibleSolutionSet`, that one having met `F_{d(k+1)}` already. The paper calls
both `FSS`; here `predictedSolutionSet … k` is the printed `FSS_{k+1}`.

## References

* [1] J. M. Bravo, T. Alamo and E. F. Camacho. "Bounded error identification of systems with
      time-varying parameters". IEEE Transactions on Automatic Control, 51(7):1144-1150, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P_0 = Θ₀`, `P_{k+1} = (P_k ∩ F_{d(k+1)}) ⊕ γ Bⁿ`, the strips of measurement `k + 1`. -/
def predictedSolutionSet (Θ₀ : Set (Vec ℝ n)) (r : ℕ → Vec ℝ n) (y : ℕ → ℝ) (σ : ℝ)
    (γ : Vec ℝ n) : ℕ → Set (Vec ℝ n)
  | 0 => Θ₀
  | k + 1 => (predictedSolutionSet Θ₀ r y σ γ k ∩ {θ | |r (k + 1) ⬝ᵥ θ - y (k + 1)| ≤ σ}) +
      {b | ∀ i, |b i| ≤ γ i}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

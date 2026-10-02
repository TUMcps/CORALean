import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Peano–Baker terms of an input

What an input `u` contributes to `x' = A(t) x + u(t)` from time `0`, order by
order: `V_0(s) = ∫₀ˢ u(σ) dσ`, then `V_{k+1}(s) = ∫₀ˢ A(σ) V_k(σ) dσ` — Picard's
iteration on the input alone, the iterated integral of `A(σ₁) ⋯ A(σ_k) u(σ_{k+1})`
over the ordered simplex of `k + 1` times. At a constant `A` they are
`∫₀ˢ (s-σ)^k/k! A^k u(σ) dσ`, the orders of the variation-of-constants integral.

Vector-valued, so the integrals are Mathlib's own; only the matrix-valued
`peanoBakerTerm` has to be taken entry by entry.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `V_0(s) = ∫₀ˢ u`, `V_{k+1}(s) = ∫₀ˢ A(σ) V_k(σ) dσ`. -/
noncomputable def MatExp.peanoBakerInputTerm (A : ℝ → Mat ℝ n n) (u : ℝ → Vec ℝ n) :
    ℕ → ℝ → Vec ℝ n
  | 0 => fun s => ∫ σ in (0:ℝ)..s, u σ
  | k + 1 => fun s => ∫ σ in (0:ℝ)..s, A σ *ᵥ MatExp.peanoBakerInputTerm A u k σ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

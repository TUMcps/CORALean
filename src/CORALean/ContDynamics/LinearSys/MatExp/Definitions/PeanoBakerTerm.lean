import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Peano–Baker terms of a time-varying matrix

The `k`-th term of the Peano–Baker (Dyson) series of `x' = A(t) x` from time
`0`: the identity at `k = 0`, then `P_{k+1}(s) = ∫₀ˢ A(σ) P_k(σ) dσ` — Picard's
iteration on the fundamental matrix, which unrolls to the iterated integral of
`A(σ₁) ⋯ A(σ_k)` over the ordered simplex without ever writing the simplex down.

The integral is taken entry by entry, as a real one. Mathlib's interval
integral of a matrix-valued map cannot be stated under the `l∞` operator norm
the tree uses for matrices, whose topology is not the one `Matrix` carries.

At a constant `A` the terms are `(s A)^k / k!`, the exponential's. At a run
whose `A(σ)` ranges over a box they are what `MatExp.norm_sub_peanoBakerSum_le`
and `MatExp.peanoBakerTerm_mem_matPow` are about: the series of `'varParam'`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P_0 = 1`, `P_{k+1}(s) = ∫₀ˢ A(σ) P_k(σ) dσ`, entry by entry. -/
noncomputable def MatExp.peanoBakerTerm (A : ℝ → Mat ℝ n n) : ℕ → ℝ → Mat ℝ n n
  | 0 => fun _ => 1
  | k + 1 => fun s => Matrix.of fun i j =>
      ∫ σ in (0:ℝ)..s, (A σ * MatExp.peanoBakerTerm A k σ) i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

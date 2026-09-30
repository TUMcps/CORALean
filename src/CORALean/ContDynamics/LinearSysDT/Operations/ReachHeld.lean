import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContDynamics.Reach.Definitions.InputParams

/-!
# `reach` at one held input point

`reachHeld` is `reach` at `𝕋 = ℝ` and one held input, closed form, no
`reduce`: `U` multiplied once by `∑ i < N, Aⁱ`, not accumulated per step, so
a zero-order hold reads off exactly rather than through the jitter a fresh
point of `U` at every step would add.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reach` at one held point of `U`: `U` multiplied once by `∑ i < N, Aⁱ`, not
accumulated per step, so a zero-order hold reads off exactly rather than through
the jitter a fresh point of `U` at every step would add. -/
def LinearSysDT.reachHeld (sys : LinearSysDT ℝ n)
    (params : Reach.InputParams (S n) (S n) ℕ) : S n :=
  let R₀ := params.R0                                               -- the paper's symbols
  let U := params.U
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  plus (mtimes (sys.A ^ N) R₀) (mtimes (∑ i ∈ Finset.range N, sys.A ^ i) U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

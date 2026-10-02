import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The input's contribution accumulated up to the end of a window

`P^R(t_{k+1})`, the particular solution at the right end of window `τ_k`, grown
one window at a time from `P^R(Δt)`, `inputSolution`'s set:
`P^R(t_{k+1}) = P^R(t_k) ⊕ e^{A t_k} P^R(Δt)`, [1, Prop. 3.2] read with the new
window prepended rather than appended, which puts `e^{A t_k}` on the one-step
set and never on the accumulated one — so a representation that `mtimes` only
encloses pays for it once per window, not once per window before it. Indexed
from `0`, so that `P^R(t_0) = {0}`, a set no representation is asked to hold,
never appears.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P^R(t_{k+1})` at index `k`, windows of width `Δt` at Taylor order `η`:
`P^R(t_1) = P^R(Δt)`, and `P^R(t_{k+2}) = P^R(t_{k+1}) ⊕ e^{A t_{k+1}} P^R(Δt)`. -/
noncomputable def LinearSys.particularSolution (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ)
    (U : S n) : ℕ → S n
  | 0 => sys.inputSolution Δt η U                               -- P^R(t_1) = P^R(Δt)
  | k + 1 =>
    let PRtk := sys.particularSolution Δt η U k                -- P^R(t_{k+1})
    let tk := ((k + 1 : ℕ) : ℝ) * Δt                            -- t_{k+1}
    let PRΔt := sys.inputSolution Δt η U                        -- P^R(Δt)
    Plus.plus PRtk (Mtimes.mtimes (exp (tk • toRealMat sys.A)) PRΔt)  -- ⊕ e^{A t_{k+1}} P^R(Δt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

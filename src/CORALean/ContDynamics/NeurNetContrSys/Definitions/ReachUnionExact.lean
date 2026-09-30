import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
import CORALean.NN.Operations.Eval

/-!
# The exact set `Reach NeurNetContrSys` is asked to enclose

Every state some zero-order-hold run over at most `H` periods of length `Δtc`
reaches, at a period boundary, run at the controller's own `eval` in place of a
free `π` — `NeurNetContrSys.Trajectory`'s fields, over a bare initial set.
Positional, as the mathematics: `Reach` reads `Δtc` off the system, CORA's `sys.dt`,
and `H = tFinal - tStart` and the initial set off `params`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in at most `H` periods of length `Δtc` of the closed loop
from a bare initial set `X`, at a period boundary. -/
def NeurNetContrSys.reachUnionExact (sys : NeurNetContrSys 𝕋 S n) (Δtc : ℝ) (H : ℕ)
    (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ i ≤ H, {y | ∃ x : ℝ → Vec ℝ n, x 0 ∈ X ∧
    (∀ j < H, ∀ t ∈ Set.Icc ((j : ℝ) * Δtc) (((j : ℝ) + 1) * Δtc),
      HasDerivWithinAt x (toRealMat sys.plant.A *ᵥ x t + sys.contr.eval.out (x ((j : ℝ) * Δtc)))
        (Set.Icc ((j : ℝ) * Δtc) (((j : ℝ) + 1) * Δtc)) t) ∧
    x ((i : ℝ) * Δtc) = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

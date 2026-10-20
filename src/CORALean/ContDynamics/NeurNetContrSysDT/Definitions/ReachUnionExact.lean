module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Map
public import CORALean.NN.Operations.Eval

@[expose] public section

/-!
# The exact set `Reach NeurNetContrSysDT` is asked to enclose

Every state the closed loop reaches in at most `K` steps from a bare initial set, run at the
controller's own `eval`, the function every layer's `enclose` is checked against, under external
inputs in `U_ext` at every step. Positional, as the mathematics: `Reach` reads `K = tFinal - tStart`
and the initial set off `params`, the closed loop being time-invariant.

## Inputs
* `sys` – closed-loop system
* `K` – step bound
* `U_ext` – external input set
* `X` – initial set

## Output
* the states the closed loop reaches within `K` steps
-/

-- Authors:       Claude Sonnet 5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in at most `K` steps of the closed loop from a bare
initial set `X`, under external inputs in `U_ext`. -/
def NeurNetContrSysDT.reachUnionExact (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n) (K : ℕ)
    (U_ext : Set (Vec ℝ sys.nExt)) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ k ≤ K, {y | ∃ (x : ℕ → Vec ℝ n) (v : ℕ → Vec ℝ sys.nExt), x 0 ∈ X ∧ (∀ j, v j ∈ U_ext) ∧
    (∀ j, x (j + 1) = sys.map sys.contr.eval.out (x j) (v j)) ∧ x k = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

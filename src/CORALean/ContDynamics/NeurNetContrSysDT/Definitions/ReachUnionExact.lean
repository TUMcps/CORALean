import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
import CORALean.NN.Operations.Eval

/-!
# The exact set `Reach NeurNetContrSysDT` is asked to enclose

Every state the closed loop reaches in at most `K` steps from a bare initial set,
run at the controller's own `eval`, the function every layer's `enclose` is
checked against. Positional, as the mathematics: `Reach` reads `K = tFinal - tStart`
and the initial set off `params`, the closed loop being time-invariant.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in at most `K` steps of the closed loop from a bare
initial set `X`. -/
def NeurNetContrSysDT.reachUnionExact (sys : NeurNetContrSysDT 𝕋 S n) (K : ℕ)
    (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ k ≤ K, (sys.map sys.contr.eval.out)^[k] '' X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachParams
import CORALean.NN.Operations.Eval

/-!
# The exact set `Reach NeurNetContrSysDT` is asked to enclose

Every state the closed loop reaches in at most `p.K` steps from a bare
initial set, run at the controller's own `eval`, the function every layer's
`enclose` is checked against — the `Reach.reachExact` field of the instance.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in at most `p.K` steps of the closed loop from a
bare initial set `X`. -/
def NeurNetContrSysDT.reachUnionExact (sys : NeurNetContrSysDT 𝕋 S n)
    (p : NeurNetContrSysDT.ReachParams) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ k ≤ p.K, (sys.map sys.contr.eval.out)^[k] '' X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

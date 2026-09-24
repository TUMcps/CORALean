import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachParams
import CORALean.NN.Operations.Eval

/-!
# The exact set `Reach NeurNetContrSys` is asked to enclose

Every state some zero-order-hold run over at most `p.H` periods reaches, at a
period boundary, run at the controller's own `eval` in place of a free `π` —
`NeurNetContrSys.Trajectory`'s fields, over a bare initial set.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in at most `p.H` periods of the closed loop from a
bare initial set `X`, at a period boundary. -/
def NeurNetContrSys.reachUnionExact (sys : NeurNetContrSys 𝕋 S n)
    (p : NeurNetContrSys.ReachParams) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ i ≤ p.H, {y | ∃ x : ℝ → Vec ℝ n, x 0 ∈ X ∧
    (∀ j < p.H, ∀ t ∈ Set.Icc ((j : ℝ) * ((p.N : ℝ) * p.Δt)) (((j : ℝ) + 1) * ((p.N : ℝ) * p.Δt)),
      HasDerivWithinAt x (toRealMat sys.plant.A *ᵥ x t +
        sys.contr.eval.out (x ((j : ℝ) * ((p.N : ℝ) * p.Δt))))
        (Set.Icc ((j : ℝ) * ((p.N : ℝ) * p.Δt)) (((j : ℝ) + 1) * ((p.N : ℝ) * p.Δt))) t) ∧
    x ((i : ℝ) * ((p.N : ℝ) * p.Δt)) = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

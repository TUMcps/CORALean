module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

@[expose] public section

/-!
# `Ellipsoid.isBadDir`

CORA's `@ellipsoid/isBadDir(E1, E2, L)`: is a direction `l` bad for the Minkowski difference of
two ellipsoids. CORA takes `[~,D] = simdiag(Q1, Q2)`, the simultaneous diagonalisation with
`T Q1 Tᵀ = I` and `T Q2 Tᵀ = D`, so `max(diag(D))` is the largest generalised eigenvalue of
`(Q2, Q1)`, the largest `vᵀ Q2 v / vᵀ Q1 v`. With `r = 1/max(diag(D))`, a direction is bad when
`sqrt(lᵀ Q1 l)/sqrt(lᵀ Q2 l) > r + TOL`. The largest eigenvalue is read here as that supremum
over nonzero `v`, which is what `simdiag` computes for `Q1` positive definite and `Q2` positive
semidefinite (it throws otherwise); the tolerance `TOL` is `0`. `L` is a matrix of directions
and the result one verdict per column, so this is the verdict of one column.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The direction `l` is bad for `E₁ ⊖ E₂`. -/
noncomputable def Ellipsoid.isBadDir (E₁ E₂ : Ellipsoid n) (l : Vec ℝ n) : Prop :=
  -- `max(diag(D))` for `[~,D] = simdiag(Q1,Q2)`: the largest `vᵀ Q2 v / vᵀ Q1 v`
  let maxD : ℝ := ⨆ v : {v : Vec ℝ n // v ≠ 0},
    (v.1 ⬝ᵥ (E₂.shape *ᵥ v.1)) / (v.1 ⬝ᵥ (E₁.shape *ᵥ v.1))
  -- `r = 1/max(diag(D))`
  let r : ℝ := 1 / maxD
  -- `res(i) = sqrt(l'*E1.Q*l)/sqrt(l'*E2.Q*l) > r+TOL`, with `TOL = 0`
  r < Real.sqrt (l ⬝ᵥ (E₁.shape *ᵥ l)) / Real.sqrt (l ⬝ᵥ (E₂.shape *ᵥ l))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

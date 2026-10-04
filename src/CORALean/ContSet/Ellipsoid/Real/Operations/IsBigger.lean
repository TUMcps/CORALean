import CORALean.ContSet.Ellipsoid.Real.Operations.Shape

/-!
# `Ellipsoid.isBigger`

CORA's `@ellipsoid/isBigger`: is `E₂` inside `E₁` once both centres are moved to the origin,
`ellipsoid(E₂.Q) ⊆ ellipsoid(E₁.Q)`. CORA decides it from the simultaneous diagonalisation of
`Q₁` and `Q₂` (largest generalised eigenvalue at most `1 + tol`); what that computes, at
tolerance `0`, is the Loewner order `Q₂ ⪯ Q₁`, stated here as the quadratic forms,
`vᵀ Q₂ v ≤ vᵀ Q₁ v` for every `v`. `isBigger_iff_subset` is the link to the sets.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.isBigger (E₁ E₂ : Ellipsoid n) : Prop :=
  ∀ v : Vec ℝ n, v ⬝ᵥ (E₂.shape *ᵥ v) ≤ v ⬝ᵥ (E₁.shape *ᵥ v)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

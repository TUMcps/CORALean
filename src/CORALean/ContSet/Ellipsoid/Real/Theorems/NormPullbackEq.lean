module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose

@[expose] public section

/-!
# The pulled-back direction's length is CORA's square root

`‖Gᵀ d‖₂ = √(dᵀ Q d)`, as `‖Gᵀ d‖₂² = dᵀ G Gᵀ d` and `G Gᵀ = Q`: the generator form of the support
function's second term is CORA's `sqrt(dir'*E.Q*dir)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `‖Gᵀ d‖₂ = √(dᵀ Q d)` for the direction `d` of `c`. -/
theorem Ellipsoid.norm₂_pullback (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    ‖E.pullback c‖₂ = Real.sqrt (dualVec c ⬝ᵥ E.Q *ᵥ dualVec c) := by -- --- PROOF ---
  set d := dualVec c
  have hsq : E.pullback c ⬝ᵥ E.pullback c = d ⬝ᵥ E.Q *ᵥ d := by
    have h : (E.Gᵀ *ᵥ d) ⬝ᵥ (E.Gᵀ *ᵥ d) = d ⬝ᵥ (E.G *ᵥ (E.Gᵀ *ᵥ d)) := by
      rw [dotProduct_mulVec d E.G, mulVec_transpose]
    rw [Ellipsoid.pullback, h, mulVec_mulVec, E.G_mul_transpose]
  rw [← hsq, dotProduct_self, Real.sqrt_sq (norm₂_nonneg _)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

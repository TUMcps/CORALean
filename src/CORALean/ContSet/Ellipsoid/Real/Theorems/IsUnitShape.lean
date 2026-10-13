import CORALean.ContSet.Ellipsoid.Real.Operations.Rank
import CORALean.ContSet.Ellipsoid.Real.Theorems.DotTranspose

/-!
# The shape matrix of a full-rank ellipsoid is invertible

`Q z = 0` gives `‖Gᵀ z‖₂ = 0`, so `z` is orthogonal to everything `G` reaches, which at full rank
is the whole space.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- At full rank the shape matrix is invertible. -/
theorem Ellipsoid.isUnit_shape (E : Ellipsoid n) (hr : E.rank = n) :
    IsUnit E.shape := by -- --- PROOF ---
  -- injective: `Q z = 0` gives `‖Gᵀ z‖₂ = 0`, so `z` is orthogonal to everything `G` reaches
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro z z' hzz
  have hrange : LinearMap.range (Matrix.mulVecLin E.G) = ⊤ := by
    unfold Ellipsoid.rank Matrix.rank at hr
    exact Submodule.eq_top_of_finrank_eq (by rw [hr]; simp)
  -- one vector `d = z - z'` with `Q d = 0`
  have hd : E.shape *ᵥ (z - z') = 0 := by rw [Matrix.mulVec_sub, hzz, sub_self]
  set d := z - z' with hdd
  have hd' : E.G *ᵥ (E.Gᵀ *ᵥ d) = 0 := by
    rw [Matrix.mulVec_mulVec]
    exact hd
  have h1 : (E.Gᵀ *ᵥ d) ⬝ᵥ (E.Gᵀ *ᵥ d) = 0 := by
    rw [Ellipsoid.dot_transpose, hd', dotProduct_zero]
  have h2 : E.Gᵀ *ᵥ d = 0 := by
    rw [dotProduct_self_eq_zero] at h1
    exact h1
  -- orthogonal to everything `G` reaches, so to `d` itself
  have h3 : d ⬝ᵥ d = 0 := by
    obtain ⟨a, ha⟩ : d ∈ LinearMap.range (Matrix.mulVecLin E.G) := hrange ▸ Submodule.mem_top
    have : d ⬝ᵥ d = (E.Gᵀ *ᵥ d) ⬝ᵥ a := by
      rw [Ellipsoid.dot_transpose]
      exact congrArg (d ⬝ᵥ ·) ha.symm
    rw [this, h2, zero_dotProduct]
  have : d = 0 := dotProduct_self_eq_zero.mp h3
  exact sub_eq_zero.mp this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

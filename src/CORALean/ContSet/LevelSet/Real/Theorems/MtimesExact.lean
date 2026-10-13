import CORALean.ContSet.LevelSet.Real.Operations.Mtimes

/-!
# `LevelSet.mtimes` is exact

The image under an invertible matrix is the level set of the substituted function, with
equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

open Matrix in
theorem LevelSet.mtimes_exact (M : Mat ℝ n n) (hM : IsUnit M.det) (L : LevelSet n) :
    (L.mtimes M).construct = (M *ᵥ ·) '' L.construct := by -- --- PROOF ---
  ext y
  constructor
  · intro h
    refine ⟨M⁻¹ *ᵥ y, h, ?_⟩
    simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM]
  · rintro ⟨x, hx, rfl⟩
    intro i
    have : M⁻¹ *ᵥ (M *ᵥ x) = x := by
      simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM]
    simpa [LevelSet.mtimes, this] using hx i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

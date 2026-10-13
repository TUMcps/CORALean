import CORALean.ContSet.SpectraShadow.Real.Operations.HyperplaneOne

/-!
# `hyperplaneOne` is the hyperplane at height `1`

The inequality `0 ⪰ 0` holds for every `β`, and the point is `(β, 1)`: the set is the points of
`ℝⁿ⁺¹` whose last coordinate is `1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.hyperplaneOne_construct :
    (SpectraShadow.hyperplaneOne n).construct = {w | w (Fin.natAdd n 0) = 1} := by -- --- PROOF ---
  ext w
  constructor
  · rintro ⟨β, -, rfl⟩
    simp [SpectraShadow.hyperplaneOne]
  -- the first `n` coordinates are the coefficients
  · intro hw
    refine ⟨fun j => w (Fin.castAdd 1 j), ?_, ?_⟩
    · simp only [SpectraShadow.hyperplaneOne, smul_zero, Finset.sum_const_zero, add_zero]
      exact PosSemidef.zero
    · funext i
      induction i using Fin.addCases with
      | left p => simp [SpectraShadow.hyperplaneOne, Finset.sum_apply, Pi.single_apply]
      | right q =>
        obtain rfl : q = 0 := Subsingleton.elim _ _
        simpa [SpectraShadow.hyperplaneOne] using hw

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

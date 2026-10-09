import CORALean.Global.BlockDiag
import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# The diagonal pair is linear in the vector it carries

`β`-weighted sums of `blockDiag (diagonal gᵢ) (diagonal (-gᵢ))` are the block diagonal at the
weighted sum of the `gᵢ`: what `inter` uses to write an equality `e = 0` as `e ⪰ 0` and `-e ⪰ 0`,
and `generateESumRep` the same.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.eq_block_sum {ι : Type} (s : Finset ι) (β : ι → ℝ) (g : ι → Vec ℝ n) :
    ∑ i ∈ s, β i • blockDiag 0 (diagonal (g i)) (diagonal (-(g i)))
      = blockDiag 0 (diagonal (∑ i ∈ s, β i • g i))
        (diagonal (-(∑ i ∈ s, β i • g i))) := by -- --- PROOF ---
  -- the diagonal matrix is linear in its vector
  have hd : ∀ h : ι → Vec ℝ n, ∑ i ∈ s, β i • (diagonal (h i) : Mat ℝ n n)
      = diagonal (∑ i ∈ s, β i • h i) := fun h => by
    ext j k
    simp only [Matrix.sum_apply, Matrix.smul_apply, diagonal_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  -- and so is the block-diagonal pair
  simp_rw [← blockDiag_smul]
  rw [← blockDiag_sum, hd, show ∑ i ∈ s, β i • (diagonal (-(g i)) : Mat ℝ n n)
      = diagonal (-(∑ i ∈ s, β i • g i)) by
    rw [hd (fun i => -(g i))]
    congr 1
    simp [Finset.sum_neg_distrib]]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

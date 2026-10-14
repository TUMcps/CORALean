module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Generators

@[expose] public section

/-!
# The generators reproduce the covariance

`V √W · (V √W)ᵀ = V W Vᵀ = Σ` for a symmetric positive semidefinite `Σ`: the `n` probabilistic
generators of `generators` and `probReduce` span the same Gaussian as the covariance.
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

theorem ProbZonotope.generators_mul_transpose (P : ProbZonotope n) (h : P.cov.PosSemidef) :
    P.generators * P.generatorsᵀ = P.cov := by -- --- PROOF ---
  have key : ∀ (A : Mat ℝ n n) (hA : A.IsHermitian), A.PosSemidef →
      ((hA.eigenvectorUnitary : Mat ℝ n n)
        * diagonal (fun i => Real.sqrt (hA.eigenvalues i)))
      * ((hA.eigenvectorUnitary : Mat ℝ n n)
        * diagonal (fun i => Real.sqrt (hA.eigenvalues i)))ᵀ = A := by
    intro A hA hP
    have hspec := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    simp only [RCLike.ofReal_real_eq_id, Function.id_comp] at hspec
    -- the square roots multiply back to the eigenvalues
    have hD : diagonal (fun i => Real.sqrt (hA.eigenvalues i))
        * (diagonal (fun i => Real.sqrt (hA.eigenvalues i)))
        = diagonal hA.eigenvalues := by
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      exact Real.mul_self_sqrt (hP.eigenvalues_nonneg i)
    have hT : (hA.eigenvectorUnitary : Mat ℝ n n)ᵀ = star (hA.eigenvectorUnitary : Mat ℝ n n) := by
      rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    -- expand `V √W (V √W)ᵀ` against the spectral theorem
    conv_rhs => rw [hspec]
    rw [transpose_mul, diagonal_transpose, hT, Matrix.mul_assoc, ← Matrix.mul_assoc
      (diagonal _), hD]
    simp [Matrix.mul_assoc]
  -- the symmetrization of a symmetric matrix is itself
  have hsym : (2 : ℝ)⁻¹ • (P.cov + P.covᵀ) = P.cov := by
    have : P.covᵀ = P.cov := by
      have := h.isHermitian.eq
      rwa [conjTranspose_eq_transpose_of_trivial] at this
    rw [this, ← two_smul ℝ, smul_smul]; norm_num
  unfold ProbZonotope.generators
  have hP : ((2 : ℝ)⁻¹ • (P.cov + P.covᵀ)).PosSemidef := by rw [hsym]; exact h
  rw [key _ _ hP, hsym]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

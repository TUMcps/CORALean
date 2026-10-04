import CORALean.Global.DmdcFit
import CORALean.Global.DmdReduced

/-!
# The reduced-order model and the dynamic modes of the dynamic mode decomposition with control

With `[Ā, B̄]` the blocks of `Ḡ` [1, Eq. 28] and an orthonormal basis `Û` of the output
space, the reduced model `Ã = Ûᵀ Ā Û` [1, Eq. 29], `B̃ = Ûᵀ B̄` [1, Eq. 30] is the full one seen
in `x = Û x̃`: `x̃_{k+1} = Ã x̃_k + B̃ u_k` [1, Eq. 31]; the same step with a known `B`
[1, Eq. 20-23]. If `Û` spans the columns of `X'` (the full rank of the output SVD, no
truncation) the dynamic modes `φ = Ā Û w`, `Ã w = λ w` [1, Eq. 32], in matrix form
[1, Eq. 36], are eigenvectors of `Ā` for `λ`, and nonzero for `λ ≠ 0`. Real eigenpairs only.

## References

* [1] J. L. Proctor, S. L. Brunton and J. N. Kutz. "Dynamic mode decomposition with control".
      SIAM Journal on Applied Dynamical Systems, 15(1):142-161, 2016 (arXiv:1409.6358).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n l N r p k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 31], [1, Eq. 20-23]: projecting the step of the full model by `Ûᵀ` is the step of the
reduced one, for `x = Û xt`. -/
theorem dmdc_reduced_step (Ā : Mat ℝ n n) (Bb : Mat ℝ n l) (Û : Mat ℝ n r) (xt : Vec ℝ r)
    (u : Vec ℝ l) :
    Ûᵀ *ᵥ (Ā *ᵥ (Û *ᵥ xt) + Bb *ᵥ u) = (Ûᵀ * Ā * Û) *ᵥ xt + (Ûᵀ * Bb) *ᵥ u := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- [1, Eq. 29]: `Ã = Ûᵀ Ā Û = Ûᵀ X' Ṽ Σ̃⁻¹ Ũ₁ᵀ Û`. -/
theorem dmdc_reducedA_eq (X2 : Mat ℝ n N) (V : Mat ℝ (n + l) p) (s : Fin p → ℝ) (W : Mat ℝ N p)
    (Û : Mat ℝ n r) :
    Ûᵀ * (dmdcBlocks (dmdCandidate X2 V s W p)).1 * Û
      = Ûᵀ * X2 * W * Matrix.diagonal (fun i : Fin p => if (i : ℕ) < p then (s i)⁻¹ else 0)
        * (Matrix.of fun a j => V (Fin.castAdd l a) j)ᵀ * Û := by
  rw [dmdcBlocks_candidate]
  simp only [Matrix.mul_assoc]

/-- [1, Eq. 30]: `B̃ = Ûᵀ B̄ = Ûᵀ X' Ṽ Σ̃⁻¹ Ũ₂ᵀ`. -/
theorem dmdc_reducedB_eq (X2 : Mat ℝ n N) (V : Mat ℝ (n + l) p) (s : Fin p → ℝ) (W : Mat ℝ N p)
    (Û : Mat ℝ n r) :
    Ûᵀ * (dmdcBlocks (dmdCandidate X2 V s W p)).2
      = Ûᵀ * X2 * W * Matrix.diagonal (fun i : Fin p => if (i : ℕ) < p then (s i)⁻¹ else 0)
        * (Matrix.of fun b j => V (Fin.natAdd n b) j)ᵀ := by
  rw [dmdcBlocks_candidate]
  simp only [Matrix.mul_assoc]

/-- [1, Eq. 36]: if `Û Ûᵀ Ā = Ā` (the range of `Ā` lies in the span of `Û`) then for
`Ã W = W Λ`, `Ã = Ûᵀ Ā Û`, the columns of `Ā Û W` are eigenvectors of `Ā`:
`Ā (Ā Û W) = (Ā Û W) Λ`. -/
theorem dmdc_mode_proj (Ā : Mat ℝ n n) (Û : Mat ℝ n r) (W : Mat ℝ r k) (Λ : Mat ℝ k k)
    (hspan : Û * Ûᵀ * Ā = Ā) (h : (Ûᵀ * Ā * Û) * W = W * Λ) :
    Ā * (Ā * Û * W) = (Ā * Û * W) * Λ := by
  calc Ā * (Ā * Û * W) = Ā * (Û * Ûᵀ * Ā * Û * W) := by rw [hspan]
    _ = Ā * Û * ((Ûᵀ * Ā * Û) * W) := by simp only [Matrix.mul_assoc]
    _ = Ā * Û * (W * Λ) := by rw [h]
    _ = Ā * Û * W * Λ := by simp only [Matrix.mul_assoc]

/-- [1, Eq. 32]: one eigenpair `Ã w = λ w`; the mode `Ā Û w` is an eigenvector of `Ā`, nonzero
when `λ ≠ 0` and `w ≠ 0`. -/
theorem dmdc_mode_proj_vec (Ā : Mat ℝ n n) (Û : Mat ℝ n r) (w : Vec ℝ r) (lam : ℝ)
    (hspan : Û * Ûᵀ * Ā = Ā) (h : (Ûᵀ * Ā * Û) *ᵥ w = lam • w) :
    Ā *ᵥ ((Ā * Û) *ᵥ w) = lam • ((Ā * Û) *ᵥ w) ∧
      (lam ≠ 0 → w ≠ 0 → (Ā * Û) *ᵥ w ≠ 0) := by -- --- PROOF ---
  refine ⟨?_, fun hl hw hφ => ?_⟩
  · have e : Ā * (Ā * Û) = (Ā * Û) * (Ûᵀ * Ā * Û) := by
      calc Ā * (Ā * Û) = Ā * (Û * Ûᵀ * Ā * Û) := by rw [hspan]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul]
  · have hZ : lam • w = 0 := by
      rw [← h, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hφ, Matrix.mulVec_zero]
    exact (smul_eq_zero.mp hZ).elim hl hw

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

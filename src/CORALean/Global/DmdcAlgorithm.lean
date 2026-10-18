module

public import CORALean.Global.DmdcReduced

@[expose] public section

/-!
# The algorithm of the dynamic mode decomposition with control

The six steps of [1, Sec. III-D], the SVDs of `Ω` (`Ũ Σ̃ Ṽᵀ`, truncated at `p` by zeroing the
triples past it) and of `X'` (`Û`) and the eigenvectors `W` of `Ã` being arguments: a
factorization is not computed here, and not unique. It returns `Ã` [1, Eq. 33], `B̃`
[1, Eq. 34] and the modes `Φ` [1, Eq. 36]. They are `Ûᵀ Ā Û`, `Ûᵀ B̄` and `Ā Û W` for the
blocks `[Ā, B̄]` of `Ḡ` [1, Eq. 28]; and if `Û` spans the columns of `X'` and `Ã W = W Λ`
[1, Eq. 35] then `Ā Φ = Φ Λ`. The paper's truncation is `p`; the guarantees about the fit
of the data (`dmdcUnknownB_fit`) are at the full rank.

## References

* [1] J. L. Proctor, S. L. Brunton and J. N. Kutz. "Dynamic mode decomposition with control".
      SIAM Journal on Applied Dynamical Systems, 15(1):142-161, 2016 (arXiv:1409.6358).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n l N r p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. III-D]: `(Atl, Btl, Φ)`. -/
noncomputable def dmdcAlgorithm (xNext : Fin N → Vec ℝ n) (Vω : Mat ℝ (n + l) r)
    (s : Fin r → ℝ) (Wω : Mat ℝ N r) (p : ℕ) (Û : Mat ℝ n q) (W : Mat ℝ q q) :
    Mat ℝ q q × Mat ℝ q l × Mat ℝ n q :=
  let X' := dmdcCols xNext                                        -- step 1, `X'`
  -- steps 2 and 3: the SVDs of `Ω` (`Vω`, `s`, `Wω`) and of `X'` (`Û`) are the arguments
  let K := X' * Wω * Matrix.diagonal (fun i : Fin r => if (i : ℕ) < p then (s i)⁻¹ else 0)
  let U₁ := (Matrix.of fun a j => Vω (Fin.castAdd l a) j : Mat ℝ n r)   -- `Ũ₁`
  let U₂ := (Matrix.of fun b j => Vω (Fin.natAdd n b) j : Mat ℝ l r)    -- `Ũ₂`
  let Atl := Ûᵀ * K * U₁ᵀ * Û                                       -- (33)
  let Btl := Ûᵀ * K * U₂ᵀ                                           -- (34)
  -- step 5: `Ã W = W Λ` is the argument `W`
  let Φ := K * U₁ᵀ * Û * W                                        -- (36)
  (Atl, Btl, Φ)

/-- The outputs are `Ûᵀ Ā Û`, `Ûᵀ B̄` and `Ā Û W` for the blocks of `Ḡ = X' Ṽ Σ̃⁻¹ Ũᵀ`. -/
theorem dmdcAlgorithm_eq (xNext : Fin N → Vec ℝ n) (Vω : Mat ℝ (n + l) r) (s : Fin r → ℝ)
    (Wω : Mat ℝ N r) (p : ℕ) (Û : Mat ℝ n q) (W : Mat ℝ q q) : -- --- STMT ---
    dmdcAlgorithm xNext Vω s Wω p Û W
      = (Ûᵀ * (dmdcBlocks (dmdCandidate (dmdcCols xNext) Vω s Wω p)).1 * Û,
         Ûᵀ * (dmdcBlocks (dmdCandidate (dmdcCols xNext) Vω s Wω p)).2,
         (dmdcBlocks (dmdCandidate (dmdcCols xNext) Vω s Wω p)).1 * Û * W) := by -- --- PROOF ---
  rw [dmdcBlocks_candidate]
  unfold dmdcAlgorithm
  simp only [Matrix.mul_assoc]

/-- [1, Eq. 35] and [1, Eq. 36]: if `Û Ûᵀ X' = X'` and `Ã W = W Λ`, the columns of `Φ` are
eigenvectors of `Ā`, `Ā Φ = Φ Λ`. -/
theorem dmdcAlgorithm_modes (xNext : Fin N → Vec ℝ n) (Vω : Mat ℝ (n + l) r) (s : Fin r → ℝ)
    (Wω : Mat ℝ N r) (p : ℕ) (Û : Mat ℝ n q) (W Λ : Mat ℝ q q)
    (hspan : Û * Ûᵀ * dmdcCols xNext = dmdcCols xNext)
    (h : (dmdcAlgorithm xNext Vω s Wω p Û W).1 * W = W * Λ) : -- --- STMT ---
    (dmdcBlocks (dmdCandidate (dmdcCols xNext) Vω s Wω p)).1
        * (dmdcAlgorithm xNext Vω s Wω p Û W).2.2
      = (dmdcAlgorithm xNext Vω s Wω p Û W).2.2 * Λ := by -- --- PROOF ---
  rw [dmdcAlgorithm_eq] at h ⊢
  refine dmdc_mode_proj _ Û W Λ ?_ h
  have hA : (dmdcBlocks (dmdCandidate (dmdcCols xNext) Vω s Wω p)).1
      = dmdcCols xNext * (Wω * Matrix.diagonal
          (fun i : Fin r => if (i : ℕ) < p then (s i)⁻¹ else 0)
          * (Matrix.of fun a j => Vω (Fin.castAdd l a) j)ᵀ) := by
    rw [dmdcBlocks_candidate]
    simp only [Matrix.mul_assoc]
  rw [hA, ← Matrix.mul_assoc, hspan]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

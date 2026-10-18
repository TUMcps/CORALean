module

public import CORALean.ContSet.Zonotope.Real.Operations.StripGain
public import CORALean.ContSet.Zonotope.Real.Operations.IntersectStrip
public import CORALean.ContSet.Zonotope.Real.Theorems.LuenbergerGainOptimal

@[expose] public section

/-!
# The strip gain minimizes the Frobenius norm

[1, Eq. 38]: the gain `Λₛ = Ĝ Ĝᵀ Γᵀ (Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ)⁻¹` of the strip-based observer
minimizes the Frobenius norm of `Ḡ = [(I - Λ Γ) Ĝ, Λ R]`, the generators of
`Zonotope.intersectStrip` at the strips `|Γ x - y| ≤ φ`, `R = diag φ`. It is `[1, Prop. 2]`
at `F = I` and no process noise, whose cost is the same up to the sign of the `Λ R` block; the
invertibility of `Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ` is the formula's.

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The strip update and the Luenberger step at `F = I` have the same squared generators. -/
theorem Zonotope.aux_frobSq_intersectStrip (Γ : Mat ℝ p n) (φ y : Vec ℝ p) (Λ : Mat ℝ n p)
    (X : Zonotope (Vec ℝ n)) : -- --- STMT ---
    ∑ i, ∑ k, ((Zonotope.intersectStrip Γ φ y Λ X).G k i) ^ 2 =
      ∑ i, ∑ k, ((Zonotope.luenbergerUpdate 1 Γ Λ (0 : Mat ℝ n 0) (Matrix.diagonal φ) y X).G k i)
        ^ 2 := by -- --- PROOF ---
  refine Finset.sum_congr rfl fun i _ => ?_
  show ∑ k : Fin (X.h + p), _ = ∑ k : Fin (X.h + p + 0), _
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Zonotope.intersectStrip, Zonotope.luenbergerUpdate, Fin.append_left,
    Fin.append_right, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  -- the strip column `Λ φⱼ eⱼ` against the column `-(Λ diag φ)ⱼ`
  simp [Matrix.mul_diagonal, Matrix.mulVec_single, mul_comm]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.stripGain_optimal (Γ : Mat ℝ p n) (φ y : Vec ℝ p) (X : Zonotope (Vec ℝ n))
    (hS : IsUnit (Γ * (Matrix.of fun i j => X.G j i) * (Matrix.of fun i j => X.G j i)ᵀ * Γᵀ +
      Matrix.diagonal φ * (Matrix.diagonal φ)ᵀ).det) (Λ' : Mat ℝ n p) : -- --- STMT ---
    ∑ i, ∑ k, ((Zonotope.intersectStrip Γ φ y (Zonotope.stripGain Γ (Matrix.diagonal φ) X) X).G k
        i) ^ 2 ≤
      ∑ i, ∑ k, ((Zonotope.intersectStrip Γ φ y Λ' X).G k i) ^ 2 := by -- --- PROOF ---
  rw [Zonotope.aux_frobSq_intersectStrip, Zonotope.aux_frobSq_intersectStrip]
  -- `F = I`: the Luenberger gain is the strip gain
  have hgain : Zonotope.stripGain Γ (Matrix.diagonal φ) X =
      Zonotope.luenbergerGain 1 Γ (Matrix.diagonal φ) X := by
    simp [Zonotope.stripGain, Zonotope.luenbergerGain]
  rw [hgain]
  exact Zonotope.luenbergerGain_optimal 1 Γ 0 (Matrix.diagonal φ) y X hS Λ'

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

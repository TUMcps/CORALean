module

public import CORALean.ContSet.Zonotope.Float.Operations.ListQuadUp
public import CORALean.ContSet.Zonotope.Float.Operations.ListQuadDown
public import CORALean.ContSet.Zonotope.Float.Theorems.CubContractBracket

@[expose] public section

/-!
# `listQuadDown` and `listQuadUp` bracket `listQuad`

By linearity in `k`: for `a < b` the symmetrized `quadMat k a b + quadMat k b a` sums against
`Zext j k` to the contraction at `(j, a, b)` plus the one at `(j, b, a)`, for `a = b` to the one at
`(j, a, a)`, and below the diagonal it is `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.listQuad_bracket (T : Fin m → Fin n → Mat 𝕋 n n) (Zext : Fin N → Vec 𝕋 n)
    (i : Fin m) (j a b : Fin N) :
    toReal (Zonotope.listQuadDown T Zext i j a b)
        ≤ ∑ k, (if a < b then
              toRealVec (Zext a) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext b))
                + toRealVec (Zext b) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext a))
            else if a = b then toRealVec (Zext a) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext a))
            else 0) * toRealVec (Zext j) k
      ∧ ∑ k, (if a < b then
              toRealVec (Zext a) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext b))
                + toRealVec (Zext b) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext a))
            else if a = b then toRealVec (Zext a) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext a))
            else 0) * toRealVec (Zext j) k
        ≤ toReal (Zonotope.listQuadUp T Zext i j a b) := by -- --- PROOF ---
  have h1 := Zonotope.cubContract_bracket T (Zext j) (Zext a) (Zext b) i
  have h2 := Zonotope.cubContract_bracket T (Zext j) (Zext b) (Zext a) i
  have h3 := Zonotope.cubContract_bracket T (Zext j) (Zext a) (Zext a) i
  -- above the diagonal: the pair and its transpose
  by_cases hab : a < b
  · have hs : ∑ k, (toRealVec (Zext a) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext b))
          + toRealVec (Zext b) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext a)))
          * toRealVec (Zext j) k
        = ∑ k, toReal (Zext j k) * (toRealVec (Zext a) ⬝ᵥ
            (toRealMat (T i k) *ᵥ toRealVec (Zext b)))
          + ∑ k, toReal (Zext j k) * (toRealVec (Zext b) ⬝ᵥ
            (toRealMat (T i k) *ᵥ toRealVec (Zext a))) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [toRealVec]; ring
    simp only [hab, if_true, Zonotope.listQuadDown, Zonotope.listQuadUp]
    rw [hs]
    exact ⟨le_trans (addDown_le_add _ _) (add_le_add h1.1 h2.1),
      le_trans (add_le_add h1.2 h2.2) (add_le_addUp _ _)⟩
  -- on the diagonal: the square; below it: zero
  · by_cases hEq : a = b
    · subst hEq
      simp only [hab, if_false, if_true, Zonotope.listQuadDown, Zonotope.listQuadUp]
      have hs : ∑ k, toRealVec (Zext a) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext a))
            * toRealVec (Zext j) k
          = ∑ k, toReal (Zext j k) * (toRealVec (Zext a) ⬝ᵥ
            (toRealMat (T i k) *ᵥ toRealVec (Zext a))) :=
        Finset.sum_congr rfl fun k _ => by simp only [toRealVec]; ring
      rw [hs]
      exact ⟨h3.1, h3.2⟩
    · simp only [hab, hEq, if_false, Zonotope.listQuadDown, Zonotope.listQuadUp, zero_mul,
        Finset.sum_const_zero, toReal_zero]
      exact ⟨le_rfl, le_rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

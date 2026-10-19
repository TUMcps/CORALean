module

public import CORALean.ContSet.Zonotope.Float.Operations.TensorMultiplication
public import CORALean.ContSet.Zonotope.Float.Theorems.CubContractBracket
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.TensorMultiplication

@[expose] public section

/-!
# `tensorHDown` and `tensorHUp` bracket the generators of `tensorMultiplication`

`tildeH` of a permutation is the cubic contraction of its three generators through the tensor's
slices (`cubContract_bracket`, the triple sum regrouped); the column sums it over the permutations
mapped to it, each sum rounded the same way, so the exact column of the exact layer's
`tensorMultiplication` on the read-back operand lies between the two stored ones.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.tensorH_bracket (M : Tensor3 𝕋 n) (Z : Zonotope (Vec 𝕋 n))
    (L : Real.Zonotope.TensorLists Z.h) (iDim : Fin n) (cInd : Fin L.C) : -- --- CONCL ---
    toReal (Zonotope.tensorHDown M Z L iDim cInd)
        ≤ (Real.Zonotope.tensorMultiplication (nominal Z : Real.Zonotope (Vec ℝ n))
            (fun i a b c => toReal (M i a b c)) L).G cInd iDim
      ∧ (Real.Zonotope.tensorMultiplication (nominal Z : Real.Zonotope (Vec ℝ n))
            (fun i a b c => toReal (M i a b c)) L).G cInd iDim
        ≤ toReal (Zonotope.tensorHUp M Z L iDim cInd) := by -- --- PROOF ---
  -- `tildeH` of one permutation, bracketed by the contraction
  have hT : ∀ p : Fin L.P,
      toReal (Zonotope.cubContractDown M (Z.G (L.perm p 0)) (Z.G (L.perm p 1))
          (Z.G (L.perm p 2)) iDim)
        ≤ ∑ a, ∑ b, ∑ c, toReal (M iDim a b c) * toReal (Z.G (L.perm p 0) a)
          * toReal (Z.G (L.perm p 1) b) * toReal (Z.G (L.perm p 2) c)
      ∧ ∑ a, ∑ b, ∑ c, toReal (M iDim a b c) * toReal (Z.G (L.perm p 0) a)
          * toReal (Z.G (L.perm p 1) b) * toReal (Z.G (L.perm p 2) c)
        ≤ toReal (Zonotope.cubContractUp M (Z.G (L.perm p 0)) (Z.G (L.perm p 1))
          (Z.G (L.perm p 2)) iDim) := by
    intro p
    have hb := Zonotope.cubContract_bracket M (Z.G (L.perm p 0)) (Z.G (L.perm p 1))
      (Z.G (L.perm p 2)) iDim
    -- the regrouping of the triple sum
    have hs : ∑ k, toReal (Z.G (L.perm p 0) k) * (toRealVec (Z.G (L.perm p 1)) ⬝ᵥ
          (toRealMat (M iDim k) *ᵥ toRealVec (Z.G (L.perm p 2))))
        = ∑ a, ∑ b, ∑ c, toReal (M iDim a b c) * toReal (Z.G (L.perm p 0) a)
          * toReal (Z.G (L.perm p 1) b) * toReal (Z.G (L.perm p 2) c) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [toRealVec, toRealMat]
      ring
    rw [hs] at hb
    exact hb
  simp only [Zonotope.tensorHDown, Zonotope.tensorHUp, Real.Zonotope.tensorMultiplication]
  -- the column: the permutations mapped to it, among all of them
  rw [Finset.sum_filter, Finset.sum_apply]
  constructor
  · refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun p _ => ?_)
    by_cases hp : L.map p = cInd
    · simp only [hp, if_true]
      exact (hT p).1
    · simp [hp, toReal_zero]
  · refine le_trans (Finset.sum_le_sum fun p _ => ?_) (sum_le_sumUp _)
    by_cases hp : L.map p = cInd
    · simp only [hp, if_true]
      exact (hT p).2
    · simp [hp, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

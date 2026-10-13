import CORALean.ContSet.Capsule.Float.Operations.Mtimes
import CORALean.ContSet.Capsule.Real.Theorems.MtimesOuter
import CORALean.ContSet.Capsule.Real.Theorems.ConstructSubsetOfDistLe

/-!
# `Capsule.mtimes` encloses the image

The exact layer's `mtimes_outer` at the nominal capsule and the matrix the floats denote, then
`construct_subset_of_dist_le` to the stored capsule: the centre and the generator are each
within the length of their per-entry gap, and the radius times the exact Frobenius norm is under
the radius times its rounded-up bound. A negative radius denotes `∅`, so a point in the capsule
has `0 ≤ r`, which the product with the bound needs.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_mulVec_gap_le (k : ℕ) (M : Mat 𝕋 m n) (v : Vec 𝕋 n) :
    ‖(toRealMat M *ᵥ toRealVec v) - toRealVec (mulVecDown M v)‖₂ ≤
      toReal (normUp k fun i => subUp (dotUp (M i) v) (mulVecDown M v i)) := by -- --- PROOF ---
  refine norm₂_le_normUp k fun i => ?_
  have h₁ := dotDown_le (M i) v
  have h₂ := le_dotUp (M i) v
  have h₃ := sub_le_subUp (dotUp (M i) v) (dotDown (M i) v)
  have hv : (toRealMat M *ᵥ toRealVec v) i = ∑ j, toReal (M i j) * toReal (v j) := rfl
  show |(toRealMat M *ᵥ toRealVec v) i - toReal (dotDown (M i) v)| ≤
    |toReal (subUp (dotUp (M i) v) (dotDown (M i) v))|
  rw [hv]
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

private theorem aux_frobenius_le (k : ℕ) (M : Mat 𝕋 m n) :
    Real.sqrt (∑ i, ∑ j, toReal (M i j) ^ 2) ≤
      toReal (sqrtUp k (sumUp fun i => sqSumUp fun j => absolute (M i j))) := by
  refine le_trans (Real.sqrt_le_sqrt ?_) (le_sqrtUp k _)
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
  exact sq_sum_le_sqSumUp (v := fun j => toReal (M i j)) (m := fun j => absolute (M i j))
    fun j => by rw [toReal_absolute]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.mtimes_outer (k : ℕ) (M : Mat 𝕋 m n) (C : Capsule 𝕋 n) :
    (toRealMat M *ᵥ ·) '' C.construct ⊆ (C.mtimes k M).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  -- the exact layer's enclosure, and a point of a capsule has a nonnegative radius
  have hK := CORALean.Real.Capsule.mtimes_outer (toRealMat M) C.nominal ⟨x, hx, rfl⟩
  have hr : 0 ≤ toReal C.r := by
    obtain ⟨t, _, hle⟩ := hx
    exact le_trans (CORALean.norm₂_nonneg _) hle
  refine CORALean.Real.Capsule.construct_subset_of_dist_le (C := ⟨_, _, _⟩) ?_ hK
  -- the three lengths: the centre's gap, the generator's gap, and the scaled radius
  have h₁ := aux_mulVec_gap_le k M C.c
  have h₂ := aux_mulVec_gap_le k M C.g
  have h₃ : toReal C.r * Real.sqrt (∑ i, ∑ j, toReal (M i j) ^ 2) ≤
      toReal (mulUp C.r (sqrtUp k (sumUp fun i => sqSumUp fun j => absolute (M i j)))) :=
    le_trans (mul_le_mul_of_nonneg_left (aux_frobenius_le k M) hr) (mul_le_mulUp _ _)
  have s₁ := add_le_addUp (mulUp C.r (sqrtUp k (sumUp fun i => sqSumUp fun j => absolute (M i j))))
    (normUp k fun i => subUp (dotUp (M i) C.c) (mulVecDown M C.c i))
  have s₂ := add_le_addUp
    (addUp (mulUp C.r (sqrtUp k (sumUp fun i => sqSumUp fun j => absolute (M i j))))
      (normUp k fun i => subUp (dotUp (M i) C.c) (mulVecDown M C.c i)))
    (normUp k fun i => subUp (dotUp (M i) C.g) (mulVecDown M C.g i))
  show ‖(toRealMat M *ᵥ toRealVec C.c) - toRealVec (mulVecDown M C.c)‖₂ +
      ‖(toRealMat M *ᵥ toRealVec C.g) - toRealVec (mulVecDown M C.g)‖₂ +
      toReal C.r * Real.sqrt (∑ i, ∑ j, toReal (M i j) ^ 2) ≤ _
  show _ ≤ toReal (addUp
    (addUp (mulUp C.r (sqrtUp k (sumUp fun i => sqSumUp fun j => absolute (M i j))))
      (normUp k fun i => subUp (dotUp (M i) C.c) (mulVecDown M C.c i)))
    (normUp k fun i => subUp (dotUp (M i) C.g) (mulVecDown M C.g i)))
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

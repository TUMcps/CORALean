module

public import CORALean.ContSet.Capsule.Float.Operations.Mtimes
public import CORALean.ContSet.Capsule.Float.Theorems.MemConstructOfSplit
public import CORALean.ContSet.Capsule.Real.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Capsule.Float.Theorems.Basic
public import CORALean.ContSet.Capsule.Float.Theorems.SmulMemSymmetric

@[expose] public section

/-!
# `Capsule.mtimes` encloses the image

A point is a point of the nominal capsule plus a point `e` of the box, and its image is the image
of each. The exact layer's `mtimes_outer` puts the first at `M c + t M g + w` with `‖w‖₂` at most
the radius times the exact Frobenius norm, which is under the radius times its rounded-up bound (a
negative radius denotes `∅`, so a point in the capsule has `0 ≤ r`, which the product with the
bound needs). What it and `M e` miss of the stored `c̃ + t g̃ + w` is `M e`, the center's rounding
`M c - c̃`, and `t (M g - g̃)`, which the three boxes of the stored box hold.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Each entry of the exact product lies between the stored `mulVecDown` and `dotUp`. -/
private theorem aux_mulVec_mem (M : Mat 𝕋 m n) (v : Vec 𝕋 n) (i : Fin m) :
    toReal (mulVecDown M v i) ≤ (toRealMat M *ᵥ toRealVec v) i ∧
      (toRealMat M *ᵥ toRealVec v) i ≤ toReal (dotUp (M i) v) :=
  ⟨dotDown_le (M i) v, le_dotUp (M i) v⟩

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
  rintro _ ⟨_, ⟨y, hy, e, he, rfl⟩, rfl⟩
  -- the exact layer's enclosure, and a point of a capsule has a nonnegative radius
  have hK := CORALean.Real.Capsule.mtimes_outer (toRealMat M) C.nominal ⟨y, hy, rfl⟩
  have hr : 0 ≤ toReal C.r := by
    obtain ⟨t, _, hle⟩ := hy
    exact le_trans (Real.sqrt_nonneg _) hle
  obtain ⟨t, ht, w, hw, hMy⟩ := Capsule.exists_split_of_mem hK
  refine Capsule.mem_construct_of_split _ ht (w := w) ?_ ?_
  · -- the radius times the exact Frobenius norm, under its rounded-up product
    have h₃ : toReal C.r * Real.sqrt (∑ i, ∑ j, toReal (M i j) ^ 2) ≤
        toReal (mulUp C.r (sqrtUp k (sumUp fun i => sqSumUp fun j => absolute (M i j)))) :=
      le_trans (mul_le_mul_of_nonneg_left (aux_frobenius_le k M) hr) (mul_le_mulUp _ _)
    exact le_trans hw h₃
  · -- the image of the box point, the center's rounding, and the generator's at `t`
    have hMe := Interval.mtimes_outer M C.I_error ⟨e, he, rfl⟩
    have hc := Interval.sub_mem_residual (stored := mulVecDown M C.c)
      (x := toRealMat M *ᵥ toRealVec C.c) (lo := mulVecDown M C.c)
      (hi := fun i => dotUp (M i) C.c) fun i => aux_mulVec_mem M C.c i
    have hg := Capsule.smul_mem_symmetric (m := fun i => subUp (dotUp (M i) C.g)
      (mulVecDown M C.g i)) (δ := toRealMat M *ᵥ toRealVec C.g - toRealVec (mulVecDown M C.g)) ht
      fun i => by
        have h := aux_mulVec_mem M C.g i
        have h' := sub_le_subUp (dotUp (M i) C.g) (mulVecDown M C.g i)
        rw [abs_le]
        simp only [Pi.sub_apply, toRealVec]
        constructor <;> linarith [h.1, h.2]
    -- the three summed into the stored box, and the difference is their sum
    have hsum := Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, hMe, _, hc, rfl⟩, _, hg,
      rfl⟩
    show _ ∈ (((Interval.mtimes M C.I_error).plus (Interval.residual (mulVecDown M C.c)
      (fun i => dotUp (M i) C.c) (mulVecDown M C.c))).plus
        (Interval.symmetric fun i => subUp (dotUp (M i) C.g) (mulVecDown M C.g i))).construct
    convert hsum using 1
    show toRealMat M *ᵥ (y + e) - (toRealVec (mulVecDown M C.c) + t • toRealVec (mulVecDown M C.g)
      + w) = _
    rw [Matrix.mulVec_add]
    funext i
    have hi := congrFun hMy i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, toRealVec, Capsule.nominal,
      CORALean.Real.Capsule.mtimes] at hi ⊢
    linear_combination hi

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

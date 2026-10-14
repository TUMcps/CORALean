module

public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
public import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLast
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadRight

@[expose] public section

/-!
# A weighted block meets the weighted constraints, on the right

The mirror of the left one, at the complementary weight `(1 - t) / 2`: the same
three row groups, each reading the second block, and the weighting column
entering with the other sign.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.smul_mem_halfScaledRight {P : HPolytope 𝕋 (Vec 𝕋 n₂)} {y : Vec ℝ n₂}
    {z : Vec ℝ n₁}
    {w t : ℝ} (hw : (1 - t) / 2 = w) (hw0 : 0 ≤ w) (hy : y ∈ P.construct) :
    Fin.append (Fin.append z (w • y)) (fun _ : Fin 1 => t)
      ∈ (HPolytope.halfScaledRight n₁ P).construct := by -- --- PROOF ---
  obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp hy
  -- the third row group is the equality's lower end, which enters negated
  have hneg : toRealMat (fun i' k => neg (P.Ae i' k)) = -toRealMat P.Ae := by
    funext i' k
    exact toReal_neg _
  refine HPolytope.mem_intersection_iff.mpr ⟨HPolytope.mem_ineqs_iff.mpr fun i => ?_,
    HPolytope.mem_intersection_iff.mpr ⟨HPolytope.mem_ineqs_iff.mpr fun i => ?_,
      HPolytope.mem_ineqs_iff.mpr fun i => ?_⟩⟩
  -- an inequality row: its own bound, times a nonnegative weight
  · rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append,
      Matrix.mulVec_smul, toReal_half]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hmul : w * (toRealMat P.A *ᵥ y) i ≤ w * toReal (P.b i) :=
      mul_le_mul_of_nonneg_left (hle i) hw0
    have hkey : w * toReal (P.b i) + toReal (P.b i) / 2 * t = toReal (P.b i) / 2 := by
      rw [← hw]; ring
    linarith
  -- the upper end of an equality row, weighted the same way
  · rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append,
      Matrix.mulVec_smul, toReal_half]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hmul : w * (toRealMat P.Ae *ᵥ y) i ≤ w * toReal (P.be.sup i) :=
      mul_le_mul_of_nonneg_left (heq i).2 hw0
    have hkey : w * toReal (P.be.sup i) + toReal (P.be.sup i) / 2 * t
        = toReal (P.be.sup i) / 2 := by
      rw [← hw]; ring
    linarith
  -- and its lower end, where the weight multiplies the bound the other way
  · rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append, hneg,
      Matrix.neg_mulVec, Matrix.mulVec_smul, toReal_neg, toReal_half]
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    have hmul : w * toReal (P.be.inf i) ≤ w * (toRealMat P.Ae *ᵥ y) i :=
      mul_le_mul_of_nonneg_left (heq i).1 hw0
    have hkey : -(toReal (P.be.inf i) / 2) * t + toReal (P.be.inf i) / 2
        = w * toReal (P.be.inf i) := by
      rw [← hw]; ring
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AddSubMemNominalSet
public import CORALean.ContSet.Ellipsoid.Real.Operations.OfFactor
public import CORALean.ContSet.InflatedContSet.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# The float ball holds the real one

`Ellipsoid.ball n r` stores the shape `r²` rounded up, so its shape minus the real `r² I` is a
nonnegative diagonal, and `Ellipsoid.add_sub_mem_nominalSet` puts the real ball inside. The error
box is the origin, so the nominal part is inside the whole. The shape is also positive
semi-definite, which `Ellipsoid.spectraShadow_exact` asks for.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored shape read as reals: `toReal (r²↑)` on the diagonal. -/
private theorem aux_toRealMat_ball_Q (r : 𝕋) :
    toRealMat ((Ellipsoid.ball n r).Q : Mat 𝕋 n n) = diagonal fun _ => toReal (mulUp r r) := by
  funext i l
  exact toReal_diagonalBlock (fun _ => mulUp r r) i l


-- =======================================  MAIN THEOREM  ======================================= --

/-- The real ball `ellipsoid((toReal r)² I)` lies in the float one. -/
theorem Ellipsoid.ball_contains (r : 𝕋) :
    (Real.Ellipsoid.ofFactor (toReal r • (1 : Mat ℝ n n)) 0).construct
      ⊆ (Ellipsoid.ball n r).construct := by -- --- PROOF ---
  intro x hx
  -- the stored shape dominates `r² I`: its diagonal is rounded up from `r · r`
  have hdom : (toRealMat (Ellipsoid.ball n r).Q
      - (Real.Ellipsoid.ofFactor (toReal r • (1 : Mat ℝ n n)) 0).Q).PosSemidef := by
    have hF : (Real.Ellipsoid.ofFactor (toReal r • (1 : Mat ℝ n n)) 0).Q
        = diagonal fun _ => toReal r * toReal r := by
      show (toReal r • (1 : Mat ℝ n n)) * (toReal r • (1 : Mat ℝ n n))ᵀ = _
      rw [transpose_smul, transpose_one, smul_mul_smul_comm, mul_one, smul_one_eq_diagonal]
    rw [aux_toRealMat_ball_Q, hF, diagonal_sub]
    exact PosSemidef.diagonal fun _ => sub_nonneg.mpr (mul_le_mulUp r r)
  have h := Ellipsoid.add_sub_mem_nominalSet (E := Ellipsoid.ball n r) (Or.inr hdom) hx
  -- the center is `0`, both stored and real, and the box is the origin
  have hq : toRealVec (Ellipsoid.ball n r).q = 0 := funext fun _ => toReal_zero
  have hFq : (Real.Ellipsoid.ofFactor (toReal r • (1 : Mat ℝ n n)) 0).q = 0 := rfl
  rw [hq, zero_add, hFq, sub_zero] at h
  have h0 : (0 : Vec ℝ n) ∈ (Ellipsoid.ball n r).I_error.construct := by
    show (0 : Vec ℝ n) ∈ (Interval.origin n : Interval (Vec 𝕋 n)).construct
    rw [Interval.origin_exact]
    exact Set.mem_singleton 0
  exact InflatedContSet.nominalSet_subset_construct h0 h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

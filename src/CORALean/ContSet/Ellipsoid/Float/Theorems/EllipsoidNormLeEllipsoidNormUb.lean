module

public import CORALean.ContSet.Ellipsoid.Float.Operations.EllipsoidNormUb
public import CORALean.ContSet.Ellipsoid.Real.Theorems.EllipsoidNormLeOneIff

@[expose] public section

/-!
# `Ellipsoid.ellipsoidNormUb` bounds the ellipsoid norm

The checked equation, read as reals, is `G u = p`. The ellipsoid norm is homogeneous, and
`G (u / ‖u‖₂)` is a point of the nominal ellipsoid moved to the origin, of norm at most `1`
(`CORALean.Real.Ellipsoid.ellipsoidNorm_le_one_iff`, full rank), so `p`'s is at most `‖u‖₂`,
which `normUp` bounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open scoped Matrix
open FloatOps SoundFloatArithmetic ToRat InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] [ToRat 𝕋] in
/-- The ellipsoid norm is homogeneous. -/
theorem Ellipsoid.aux_ellipsoidNorm_smul (E : CORALean.Real.Ellipsoid n) {s : ℝ} (hs : 0 ≤ s)
    (x : Vec ℝ n) : E.ellipsoidNorm (s • x) = s * E.ellipsoidNorm x := by
  simp only [CORALean.Real.Ellipsoid.ellipsoidNorm, Matrix.mulVec_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  rw [← mul_assoc, abs_mul, Real.sqrt_mul (abs_nonneg _), abs_mul_self, Real.sqrt_mul_self hs]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.ellipsoidNorm_le_ellipsoidNormUb {prec : ℕ} {E : Ellipsoid 𝕋 n}
    {p : Vec 𝕋 n} {u : Vec 𝕋 E.k} {t : 𝕋} (hr : (nominal E).rank = n)
    (h : E.ellipsoidNormUb prec p u = some t) :
    (nominal E).ellipsoidNorm (toRealVec p) ≤ toReal t := by -- --- PROOF ---
  simp only [Ellipsoid.ellipsoidNormUb] at h
  split_ifs at h with hsol
  simp only [Option.some.injEq] at h
  rw [Bool.and_eq_true] at hsol
  obtain ⟨hsol, -⟩ := hsol
  subst h
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] at hsol
  -- the equation read as reals: `G u = p`
  have hp : toRealVec p = toRealMat E.G *ᵥ toRealVec u := funext fun i => by
    have := congrArg (fun q : ℚ => (q : ℝ)) (hsol i)
    simp only [Rat.cast_sum, Rat.cast_mul, toReal_toRat] at this
    simp [Matrix.mulVec, dotProduct, toRealMat, toRealVec, this]
  have ht : ‖toRealVec u‖₂ ≤ toReal (normUp prec u) := norm₂_le_normUp prec fun _ => le_refl _
  set s := ‖toRealVec u‖₂ with hs
  rcases (norm₂_nonneg (toRealVec u)).lt_or_eq with hpos | hzero
  · -- `p = s • G w` with `w = u / s` in the unit ball
    set w : Vec ℝ E.k := s⁻¹ • toRealVec u with hw
    have hwn : ‖w‖₂ ≤ 1 := by
      rw [hw, norm₂_smul, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
    have hmem : (nominal E).q + (nominal E).G *ᵥ w ∈ (nominal E).construct := ⟨w, hwn, rfl⟩
    have hle := ((CORALean.Real.Ellipsoid.ellipsoidNorm_le_one_iff (nominal E) hr _).mpr hmem)
    have hpw : toRealVec p = s • ((nominal E).G *ᵥ w) := by
      rw [hp, hw, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      rfl
    rw [hpw, Ellipsoid.aux_ellipsoidNorm_smul _ hpos.le]
    calc s * (nominal E).ellipsoidNorm ((nominal E).G *ᵥ w) ≤ s * 1 :=
          mul_le_mul_of_nonneg_left hle hpos.le
      _ ≤ toReal (normUp prec u) := by rw [mul_one]; exact ht
  · -- `u = 0`, so `p = 0`, whose norm is `0`
    have hu0 : toRealVec u = 0 := funext fun j =>
      abs_nonpos_iff.mp (le_trans (abs_le_norm₂ _ j) hzero.symm.le)
    rw [hp, hu0, Matrix.mulVec_zero]
    simp only [CORALean.Real.Ellipsoid.ellipsoidNorm, Matrix.mulVec_zero, dotProduct_zero,
      abs_zero, Real.sqrt_zero]
    exact le_trans (norm₂_nonneg _) ht

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

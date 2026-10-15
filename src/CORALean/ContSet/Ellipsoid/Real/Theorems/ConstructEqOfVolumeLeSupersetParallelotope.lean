module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.DetNeZeroOfSupersetParallelotope
public import CORALean.ContSet.Ellipsoid.Real.Theorems.NormSqAddTraceLeOfSupersetParallelotope
public import CORALean.ContSet.Ellipsoid.Real.Theorems.VolumeEq
public import CORALean.Global.DetLeTraceDivPow
public import CORALean.Global.EqSmulOneOfDetEqTraceDivPow
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructOfFactor

@[expose] public section

/-!
# The minimum-volume ellipsoid around a parallelotope is unique

[1, Sec. III-A (Remark a)] names `E(nGGᵀ, z̄)` *the* minimum-volume ellipsoid around
`Z(G, z̄)`: any ellipsoid `{q + Fu | ‖u‖₂ ≤ 1}` around it of no larger volume is the same set.
Equal volume makes every inequality behind `isLeast_volume_superset_parallelotope` an equality:
`tr(MMᵀ) = 1`, so `w = F⁻¹(z̄ - q) = 0` and `q = z̄`; AM-GM is tight, so `MMᵀ = I/n`
(`eq_smul_one_of_det_eq_trace_div_pow`), `M = F⁻¹G`; then `K = √n M` is orthogonal and
`F = √n G Kᵀ`, which maps the unit ball onto the image of the unit ball under `√n G`.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An orthogonal `K` (`KᵀK = I`) keeps `‖·‖₂`. -/
theorem aux_norm₂_mulVec_of_orth {K : Mat ℝ n n} (hK : Kᵀ * K = 1) (v : Vec ℝ n) :
    ‖K *ᵥ v‖₂ = ‖v‖₂ := by -- --- PROOF ---
  have hsq : ∀ x : Vec ℝ n, ∑ i, x i ^ 2 = x ⬝ᵥ x := fun x => by
    simp [dotProduct, sq]
  have h : (K *ᵥ v) ⬝ᵥ (K *ᵥ v) = v ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hK, one_mulVec]
  simp only [norm₂, hsq, h]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. III-A (Remark a)]: an ellipsoid around `Z(G, z̄)` of volume at most that of
`E(nGGᵀ, z̄)` is `E(nGGᵀ, z̄)`. -/
theorem Ellipsoid.construct_eq_of_volume_le_superset_parallelotope {G F : Mat ℝ n n}
    (hG : IsUnit G.det) {z q : Vec ℝ n}
    (hsub : {x | ∃ β : Vec ℝ n, (∀ j, |β j| ≤ 1) ∧ x = z + G *ᵥ β} ⊆
      (Ellipsoid.ofFactor F q).construct)
    (hvol : MeasureTheory.volume (Ellipsoid.ofFactor F q).construct ≤
      MeasureTheory.volume (Ellipsoid.ofFactor (Real.sqrt n • G) z).construct) :
    (Ellipsoid.ofFactor F q).construct
      = (Ellipsoid.ofFactor (Real.sqrt n • G) z).construct := by -- --- PROOF ---
  rcases Nat.eq_zero_or_pos n with rfl | hn
  -- `ℝ⁰` is a point
  · rw [Ellipsoid.construct_ofFactor, Ellipsoid.construct_ofFactor]
    ext x
    exact ⟨fun _ => ⟨0, by simp [norm₂], Subsingleton.elim _ _⟩,
      fun _ => ⟨0, by simp [norm₂], Subsingleton.elim _ _⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hFu : IsUnit F.det :=
    isUnit_iff_ne_zero.mpr (Ellipsoid.det_ne_zero_of_superset_parallelotope hG hsub)
  -- the volumes: `det(F)² ≤ nⁿ det(G)²`
  have hdetF : F.det ^ 2 ≤ (n : ℝ) ^ n * G.det ^ 2 := by
    rw [Ellipsoid.volume_eq _, Ellipsoid.volume_eq _] at hvol
    unfold Ellipsoid.volume Ellipsoid.ofFactor at hvol
    have hV : 0 < Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) :=
      div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
    simp only [det_mul, det_transpose, det_smul, Fintype.card_fin] at hvol
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity), mul_le_mul_iff_right₀ hV,
      Real.sqrt_le_sqrt_iff (mul_self_nonneg _)] at hvol
    have hsq : Real.sqrt n ^ n * Real.sqrt n ^ n = (n : ℝ) ^ n := by
      rw [← mul_pow, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    nlinarith [hvol, hsq]
  set M : Mat ℝ n n := F⁻¹ * G with hMdef
  set w : Vec ℝ n := F⁻¹ *ᵥ (z - q) with hwdef
  have hsum := Ellipsoid.normSq_add_trace_le_of_superset_parallelotope hFu hsub
  rw [← hMdef, ← hwdef] at hsum
  have hPSD : (M * Mᵀ).PosSemidef := by
    simpa using posSemidef_self_mul_conjTranspose M
  -- `det(MMᵀ) = det(G)²/det(F)² ≥ n⁻ⁿ`, and `≤ (tr(MMᵀ)/n)ⁿ`
  have hMdet : (M * Mᵀ).det = G.det ^ 2 / F.det ^ 2 := by
    rw [det_mul, det_transpose, hMdef, det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    field_simp
  have hF2 : 0 < F.det ^ 2 := by have := hFu.ne_zero; positivity
  have hlow : (1 / (n : ℝ)) ^ n ≤ (M * Mᵀ).det := by
    rw [hMdet, le_div_iff₀ hF2, div_pow, one_pow, one_div_mul_eq_div,
      div_le_iff₀ (by positivity)]
    linarith
  have hup := det_le_trace_div_pow hPSD hn
  have htr0 : 0 ≤ (M * Mᵀ).trace := by simpa using hPSD.trace_nonneg
  -- hence `tr(MMᵀ) = 1`, `w = 0`, `det(MMᵀ) = (tr/n)ⁿ`
  have htr1 : 1 ≤ (M * Mᵀ).trace := by
    have h := (pow_le_pow_iff_left₀ (by positivity) (div_nonneg htr0 hn'.le) hn.ne').mp
      (hlow.trans hup)
    rwa [div_le_div_iff_of_pos_right hn'] at h
  have hw0 : ∑ i, w i ^ 2 = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have htr : (M * Mᵀ).trace = 1 := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (w i)
    linarith
  have hq : q = z := by
    have hw : w = 0 := funext fun i =>
      pow_eq_zero_iff two_ne_zero |>.mp ((Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        sq_nonneg (w j)).mp hw0 i (Finset.mem_univ i))
    have h := congrArg (F *ᵥ ·) hw
    simp only [hwdef, mulVec_mulVec, mul_nonsing_inv _ hFu, one_mulVec, mulVec_zero] at h
    exact (sub_eq_zero.mp h).symm
  have hMM : M * Mᵀ = (1 / (n : ℝ)) • (1 : Mat ℝ n n) := by
    have heq : (M * Mᵀ).det = ((M * Mᵀ).trace / n) ^ n := by
      rw [htr]; exact le_antisymm (by rw [← htr]; exact hup) hlow
    rw [eq_smul_one_of_det_eq_trace_div_pow hPSD hn heq, htr]
  -- `K = √n M` is orthogonal, and `F = √n G Kᵀ`
  set K : Mat ℝ n n := Real.sqrt n • M with hKdef
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hKK : K * Kᵀ = 1 := by
    rw [hKdef, transpose_smul, smul_mul_smul_comm, hMM, smul_smul, hs,
      mul_one_div_cancel hn'.ne', one_smul]
  have hKK' : Kᵀ * K = 1 := mul_eq_one_comm.mp hKK
  have hFK : F = Real.sqrt n • G * Kᵀ := by
    have hFM : F * M = G := by
      rw [hMdef, ← Matrix.mul_assoc, mul_nonsing_inv _ hFu, Matrix.one_mul]
    have hMK : M * Kᵀ = (Real.sqrt n)⁻¹ • (1 : Mat ℝ n n) := by
      rw [hKdef, transpose_smul, Matrix.mul_smul, hMM, smul_smul]
      congr 1
      rw [show (1 / (n : ℝ)) = 1 / (Real.sqrt n * Real.sqrt n) by rw [hs]]
      field_simp
    rw [smul_mul_assoc, ← hFM, Matrix.mul_assoc, hMK, Matrix.mul_smul, Matrix.mul_one, smul_smul,
      mul_inv_cancel₀ hspos.ne', one_smul]
  have hKT : (Kᵀ)ᵀ * Kᵀ = 1 := by rw [transpose_transpose]; exact hKK
  -- the two images of the unit ball agree
  subst hq
  rw [Ellipsoid.construct_ofFactor, Ellipsoid.construct_ofFactor]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨Kᵀ *ᵥ u, by rwa [aux_norm₂_mulVec_of_orth hKT], ?_⟩
    simp only [hFK, mulVec_mulVec]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨K *ᵥ u, by rwa [aux_norm₂_mulVec_of_orth hKK'], ?_⟩
    simp only [hFK, mulVec_mulVec, Matrix.mul_assoc, hKK', Matrix.mul_one]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

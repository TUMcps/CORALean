import CORALean.ContSet.Ellipsoid.Real.Theorems.DetNeZeroOfSupersetParallelotope
import CORALean.ContSet.Ellipsoid.Real.Theorems.NormSqAddTraceLeOfSupersetParallelotope
import CORALean.ContSet.Ellipsoid.Real.Theorems.VolumeEqSquare
import CORALean.Global.DetLeTraceDivPow

/-!
# The minimum-volume ellipsoid around a parallelotope

[1, Sec. III-A (Remark a)]: for `n = m` and `G` invertible, the minimum-volume ellipsoid enclosing
`Z(G, z̄) = {z̄ + Gβ | ‖β‖∞ ≤ 1}` is `E(nGGᵀ, z̄)`, the generator `√n G`: it encloses `Z(G, z̄)`,
and no ellipsoid `E(E, e)`, `E ≻ 0`, enclosing it has less volume. Those are the ellipsoids with a
square generator `F` (any factor of `E`); a singular `F` encloses nothing full-dimensional.
`G = I` is the hypercube and its sphere of radius `√n`, the case the remark reduces to by
`Z(I, ẑ) = G⁻¹Z(G, z̄)` (Eq. 12, `Lemma 1` at `T = G⁻¹`).

For an enclosing `E(F, q)`, `F` is invertible (`det_ne_zero_of_superset_parallelotope`) and
`tr(MMᵀ) ≤ 1` for `M = F⁻¹G` (`normSq_add_trace_le_of_superset_parallelotope`), so AM-GM on the
eigenvalues (`det_le_trace_div_pow`) gives `det(M)² ≤ n⁻ⁿ`, i.e. `|det F| ≥ nⁿᐟ²|det G|`, the volume
of `E(nGGᵀ, z̄)` over that of the unit ball. That no other ellipsoid attains it is
`construct_eq_of_volume_le_superset_parallelotope`.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An ellipsoid with a square generator `F` around the parallelotope has `nⁿ det(G)² ≤ det(F)²`. -/
theorem aux_parallelotope_det_sq_le {G F : Mat ℝ n n} (hG : IsUnit G.det) {z q : Vec ℝ n}
    (hsub : {x | ∃ β : Vec ℝ n, (∀ j, |β j| ≤ 1) ∧ x = z + G *ᵥ β} ⊆
      (⟨n, q, F⟩ : Ellipsoid n).construct) :
    (n : ℝ) ^ n * G.det ^ 2 ≤ F.det ^ 2 := by -- --- PROOF ---
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hFu : IsUnit F.det :=
    isUnit_iff_ne_zero.mpr (Ellipsoid.det_ne_zero_of_superset_parallelotope hG hsub)
  set M : Mat ℝ n n := F⁻¹ * G with hMdef
  -- `tr(MMᵀ) ≤ 1`, then AM-GM: `det(M)² = det(MMᵀ) ≤ (tr/n)ⁿ ≤ n⁻ⁿ`
  have htr : (M * Mᵀ).trace ≤ 1 := by
    have h := Ellipsoid.normSq_add_trace_le_of_superset_parallelotope hFu hsub
    have hw0 : 0 ≤ ∑ i, (F⁻¹ *ᵥ (z - q)) i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  have hPSD : (M * Mᵀ).PosSemidef := by
    simpa using posSemidef_self_mul_conjTranspose M
  have hdet : M.det ^ 2 ≤ (1 / (n : ℝ)) ^ n := by
    have h := det_le_trace_div_pow hPSD hn
    rw [det_mul, det_transpose] at h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc M.det ^ 2 = M.det * M.det := sq _
      _ ≤ ((M * Mᵀ).trace / n) ^ n := h
      _ ≤ (1 / (n : ℝ)) ^ n := by
          gcongr
          · exact div_nonneg (by simpa using hPSD.trace_nonneg) hn'.le
  -- `det M = det G / det F`, so `nⁿ det(G)² ≤ det(F)²`
  have hMdet : M.det = G.det / F.det := by
    rw [hMdef, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', inv_mul_eq_div]
  rw [hMdet, div_pow, div_le_iff₀ (by have := hFu.ne_zero; positivity)] at hdet
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ n * (1 / (n : ℝ)) ^ n = 1 := by
    rw [← mul_pow, mul_one_div_cancel hn'.ne', one_pow]
  calc (n : ℝ) ^ n * G.det ^ 2 ≤ (n : ℝ) ^ n * ((1 / (n : ℝ)) ^ n * F.det ^ 2) := by
        gcongr
    _ = F.det ^ 2 := by rw [← mul_assoc, hpow, one_mul]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. III-A (Remark a)]: `E(nGGᵀ, z̄)` encloses `Z(G, z̄)` and has the least volume of all
ellipsoids `E(E, e)`, `E ≻ 0`, that do. -/
theorem Ellipsoid.isLeast_volume_superset_parallelotope (G : Mat ℝ n n) (hG : IsUnit G.det)
    (z : Vec ℝ n) :
    IsLeast {v | ∃ (q : Vec ℝ n) (F : Mat ℝ n n),
        {x | ∃ β : Vec ℝ n, (∀ j, |β j| ≤ 1) ∧ x = z + G *ᵥ β} ⊆
          (⟨n, q, F⟩ : Ellipsoid n).construct ∧
        v = MeasureTheory.volume (⟨n, q, F⟩ : Ellipsoid n).construct}
      (MeasureTheory.volume
        (⟨n, z, Real.sqrt n • G⟩ : Ellipsoid n).construct) := by -- --- PROOF ---
  refine ⟨⟨z, Real.sqrt n • G, ?_, rfl⟩, ?_⟩
  -- the enclosure: `u = β/√n`, `‖β‖₂ ≤ √n`
  · rintro _ ⟨β, hβ, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by simp [norm₂_zero], by funext i; exact i.elim0⟩
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    refine ⟨(Real.sqrt n)⁻¹ • β, ?_, ?_⟩
    · rw [norm₂_smul, abs_inv, abs_of_pos hs, inv_mul_le_iff₀ hs, mul_one]
      have hsum : ∑ i, β i ^ 2 ≤ n := by
        calc ∑ i, β i ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
              have := hβ i
              rw [← sq_abs]; nlinarith [abs_nonneg (β i)]
          _ = n := by simp
      exact Real.sqrt_le_sqrt hsum
    · rw [smul_mulVec, mulVec_smul, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  -- least volume: `V_n |det F| ≥ V_n nⁿᐟ² |det G|`
  · rintro v ⟨q, F, hsub, rfl⟩
    rw [Ellipsoid.volume_eq_of_k_eq _ rfl, Ellipsoid.volume_eq_of_k_eq _ rfl]
    unfold Ellipsoid.volume Ellipsoid.shape
    have hV : 0 ≤ Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) :=
      div_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (Real.Gamma_nonneg_of_nonneg (by positivity))
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hV)
    simp only [det_mul, det_transpose, det_smul, Fintype.card_fin]
    have h := aux_parallelotope_det_sq_le hG hsub
    have hsq : Real.sqrt n ^ n * Real.sqrt n ^ n = (n : ℝ) ^ n := by
      rw [← mul_pow, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    calc Real.sqrt n ^ n * G.det * (Real.sqrt n ^ n * G.det)
        = (n : ℝ) ^ n * G.det ^ 2 := by rw [← hsq]; ring
      _ ≤ F.det ^ 2 := h
      _ = F.det * F.det := sq _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

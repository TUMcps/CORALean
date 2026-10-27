module

public import CORALean.Global.HMatrixRegular
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# The linear programs that extract a regular sub-matrix

[1, Eq. 14]-[1, Eq. 18]: binary `xᵢⱼ`, at most one per row and column, pick the diagonal of a
square sub-matrix of an interval matrix `A`; the constraints make it strictly dominant ((14), its
big-M form (15)) or an H-matrix ((17), and (18) at `uᵢⱼ = ⟨aᵢⱼ⟩⁻¹`), so every real matrix in it is
regular. They bound column `l` over the picked rows `i ≠ k`: the transposes of [1, Def. 4.5] and
[1, Def. 4.8]. The sub-matrix is `A.submatrix ρ κ` for injective `ρ`, `κ` whose positions `x`
picks; of `x` only `x ≥ 0` and `x(ρ t, κ t) = 1` are used. `M` plays no part in soundness, `μ > 0`
does: the printed (16) has `+μ` where (15) has `-μ` and is false (`subLp16_counterexample`).
`le_rank_of_det_submatrix_ne_zero` reads [1, Def. 4.3]: a regular sub-matrix bounds the rank.

## Inputs
* `x` – selection matrix
* `ρ` – picked rows
* `κ` – picked columns
* `mig` – matrix of mignitudes
* `mag` – matrix of magnitudes
* `A` – interval matrix representative

## Hypotheses
* `hx` – the selection is nonnegative
* `hρ` – the picked rows are distinct
* `hsel` – the picked positions are selected
* `h14` – the dominance constraint holds
* `hA` – the representative lies between the mignitudes and magnitudes

## Conclusion
* the picked sub-matrix has nonzero determinant

## References

* [1] [O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing,
      2013.](../../../references/2013/mullier-rc-general-inner-approximation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Finset Function

variable {n m k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The rows `i ≠ ρ t` of the constraint's sum reach every other picked position. -/
private theorem aux_sum_picked_le {x : Matrix (Fin n) (Fin m) ℝ} {ρ : Fin k → Fin n}
    (hρ : Injective ρ) {κ : Fin k → Fin m} (hsel : ∀ t, x (ρ t) (κ t) = 1) (f : Fin n → Fin m → ℝ)
    (hf : ∀ i j, 0 ≤ x i j * f i j) (t : Fin k) : -- --- CONCL ---
    ∑ t' ∈ univ.erase t, f (ρ t') (κ t')
      ≤ ∑ i ∈ univ.erase (ρ t), ∑ j, x i j * f i j := by -- --- PROOF ---
  calc ∑ t' ∈ univ.erase t, f (ρ t') (κ t')
      ≤ ∑ t' ∈ univ.erase t, ∑ j, x (ρ t') j * f (ρ t') j := sum_le_sum fun t' _ => by
        have := single_le_sum (fun j _ => hf (ρ t') j) (mem_univ (κ t'))
        rwa [hsel, one_mul] at this
    _ = ∑ i ∈ (univ.erase t).map ⟨ρ, hρ⟩, ∑ j, x i j * f i j :=
        (sum_map (univ.erase t) ⟨ρ, hρ⟩ (fun i => ∑ j, x i j * f i j)).symm
    _ ≤ ∑ i ∈ univ.erase (ρ t), ∑ j, x i j * f i j := by
        refine sum_le_sum_of_subset_of_nonneg (fun i hi => ?_)
          fun i _ _ => sum_nonneg fun j _ => hf i j
        obtain ⟨t', ht', rfl⟩ := mem_map.mp hi
        exact mem_erase.mpr ⟨fun h => (ne_of_mem_erase ht') (hρ h), mem_univ _⟩

/-- Column dominance at the picked positions makes every real matrix in `A` regular there. -/
private theorem aux_det_submatrix_ne_zero_of_col {x : Matrix (Fin n) (Fin m) ℝ}
    (hx : ∀ i j, 0 ≤ x i j)
    {ρ : Fin k → Fin n} (hρ : Injective ρ) {κ : Fin k → Fin m} (hsel : ∀ t, x (ρ t) (κ t) = 1)
    {mig mag : Matrix (Fin n) (Fin m) ℝ}
    (hcol : ∀ t, ∑ i ∈ univ.erase (ρ t), ∑ j, x i j * mag i (κ t) < mig (ρ t) (κ t))
    (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, mig i j ≤ |A i j| ∧ |A i j| ≤ mag i j) : -- --- CONCL ---
    (A.submatrix ρ κ).det ≠ 0 := by -- --- PROOF ---
  refine det_ne_zero_of_sum_col_lt_diag fun t => ?_
  simp only [submatrix_apply, Real.norm_eq_abs]
  calc ∑ t' ∈ univ.erase t, |A (ρ t') (κ t)| ≤ ∑ t' ∈ univ.erase t, mag (ρ t') (κ t) :=
        sum_le_sum fun t' _ => (hA _ _).2
    _ ≤ ∑ i ∈ univ.erase (ρ t), ∑ j, x i j * mag i (κ t) :=
        aux_sum_picked_le hρ hsel (fun i _ => mag i (κ t))
          (fun i j => mul_nonneg (hx i j) ((abs_nonneg _).trans (hA i (κ t)).2)) t
    _ < mig (ρ t) (κ t) := hcol t
    _ ≤ |A (ρ t) (κ t)| := (hA _ _).1


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 14], the corrected form of [1, Eq. 13] (gated on `xₖₗ = 1`):
`xₖₗ = 1 → ⟨aₖₗ⟩ > ∑_{i ≠ k} ∑ⱼ xᵢⱼ |aᵢₗ|` makes the picked sub-matrix regular. -/
theorem det_submatrix_ne_zero_of_lp14 {x : Matrix (Fin n) (Fin m) ℝ} (hx : ∀ i j, 0 ≤ x i j)
    {ρ : Fin k → Fin n} (hρ : Injective ρ) {κ : Fin k → Fin m} (hsel : ∀ t, x (ρ t) (κ t) = 1)
    {mig mag : Matrix (Fin n) (Fin m) ℝ}
    (h14 : ∀ k l, x k l = 1 → ∑ i ∈ univ.erase k, ∑ j, x i j * mag i l < mig k l)
    (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, mig i j ≤ |A i j| ∧ |A i j| ≤ mag i j) :
    (A.submatrix ρ κ).det ≠ 0 :=
  aux_det_submatrix_ne_zero_of_col hx hρ hsel (fun t => h14 _ _ (hsel t)) A hA

/-- [1, Eq. 15], the corrected form of [1, Eq. 16] (`-μ` for `+μ`): the big-M form
`∑ ≤ M + (⟨aₖₗ⟩ - μ - M) xₖₗ`, `μ > 0`, does the same. -/
theorem det_submatrix_ne_zero_of_lp15 {x : Matrix (Fin n) (Fin m) ℝ} (hx : ∀ i j, 0 ≤ x i j)
    {ρ : Fin k → Fin n} (hρ : Injective ρ) {κ : Fin k → Fin m} (hsel : ∀ t, x (ρ t) (κ t) = 1)
    {mig mag : Matrix (Fin n) (Fin m) ℝ} {M μ : ℝ} (hμ : 0 < μ)
    (h15 : ∀ k l, ∑ i ∈ univ.erase k, ∑ j, x i j * mag i l ≤ M + (mig k l - μ - M) * x k l)
    (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, mig i j ≤ |A i j| ∧ |A i j| ≤ mag i j) :
    (A.submatrix ρ κ).det ≠ 0 :=
  det_submatrix_ne_zero_of_lp14 hx hρ hsel (fun k l hkl => by
    have := h15 k l; rw [hkl, mul_one] at this; linarith) A hA

/-- [1, Eq. 17]: `∑_{i ≠ k} ∑ⱼ xᵢⱼ |aᵢₗ| uᵢⱼ ≤ M + (⟨aₖₗ⟩ uₖₗ - μ - M) xₖₗ`, `u > 0` at the picked
positions, `μ > 0`: the picked sub-matrix is an H-matrix, so regular. -/
theorem det_submatrix_ne_zero_of_lp17 {x : Matrix (Fin n) (Fin m) ℝ} (hx : ∀ i j, 0 ≤ x i j)
    {ρ : Fin k → Fin n} (hρ : Injective ρ) {κ : Fin k → Fin m} (hsel : ∀ t, x (ρ t) (κ t) = 1)
    {mig mag u : Matrix (Fin n) (Fin m) ℝ} {M μ : ℝ} (hμ : 0 < μ) (hu : ∀ i j, 0 ≤ u i j)
    (hupos : ∀ t, 0 < u (ρ t) (κ t))
    (h17 : ∀ k l, ∑ i ∈ univ.erase k, ∑ j, x i j * mag i l * u i j
      ≤ M + (mig k l * u k l - μ - M) * x k l)
    (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, mig i j ≤ |A i j| ∧ |A i j| ≤ mag i j) : -- --- CONCL ---
    (A.submatrix ρ κ).det ≠ 0 := by -- --- PROOF ---
  have hmag : ∀ i j, 0 ≤ mag i j := fun i j => (abs_nonneg _).trans (hA i j).2
  -- the transpose of the picked sub-matrix is an H-matrix, `uₜ = u(ρ t, κ t)`
  let migB : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun t _ => mig (ρ t) (κ t)
  let magB : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun t t' => mag (ρ t') (κ t)
  have hH : IsHMatrix migB magB := by
    refine ⟨fun t => u (ρ t) (κ t), hupos, fun t => ?_⟩
    rw [compMat_mulVec_apply migB magB, sub_pos]
    simp only [migB, magB, Matrix.of_apply]
    have h := h17 (ρ t) (κ t)
    rw [hsel, mul_one] at h
    calc ∑ t' ∈ univ.erase t, mag (ρ t') (κ t) * u (ρ t') (κ t')
        ≤ ∑ i ∈ univ.erase (ρ t), ∑ j, x i j * (mag i (κ t) * u i j) :=
          aux_sum_picked_le hρ hsel (fun i j => mag i (κ t) * u i j)
            (fun i j => mul_nonneg (hx i j) (mul_nonneg (hmag _ _) (hu i j))) t
      _ = ∑ i ∈ univ.erase (ρ t), ∑ j, x i j * mag i (κ t) * u i j := by
          simp only [mul_assoc]
      _ < mig (ρ t) (κ t) * u (ρ t) (κ t) := by linarith
  rw [← det_transpose]
  exact det_ne_zero_of_isHMatrix hH _ (fun t => (hA _ _).1) (fun t t' _ => (hA _ _).2)

/-- [1, Eq. 18]: (17) at `uᵢⱼ = ⟨aᵢⱼ⟩⁻¹`, with `⟨aₖₗ⟩ ≠ 0` where `x` picks ([1, Remark 4.2]). -/
theorem det_submatrix_ne_zero_of_lp18 {x : Matrix (Fin n) (Fin m) ℝ} (hx : ∀ i j, 0 ≤ x i j)
    {ρ : Fin k → Fin n} (hρ : Injective ρ) {κ : Fin k → Fin m} (hsel : ∀ t, x (ρ t) (κ t) = 1)
    {mig mag : Matrix (Fin n) (Fin m) ℝ} {M μ : ℝ} (hμ : 0 < μ) (hmig : ∀ i j, 0 ≤ mig i j)
    (h42 : ∀ t, mig (ρ t) (κ t) ≠ 0)
    (h18 : ∀ k l, ∑ i ∈ univ.erase k, ∑ j, x i j * mag i l * (mig i j)⁻¹
      ≤ M + (mig k l * (mig k l)⁻¹ - μ - M) * x k l)
    (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, mig i j ≤ |A i j| ∧ |A i j| ≤ mag i j) :
    (A.submatrix ρ κ).det ≠ 0 :=
  det_submatrix_ne_zero_of_lp17 hx hρ hsel hμ (fun i j => inv_nonneg.mpr (hmig i j))
    (fun t => inv_pos.mpr ((hmig _ _).lt_of_ne (h42 t).symm)) h18 A hA

/-- [1, Def. 4.3]: a regular `k × k` sub-matrix of every `A ∈ A` gives `rank A ≥ k`. -/
theorem le_rank_of_det_submatrix_ne_zero (A : Matrix (Fin n) (Fin m) ℝ) (ρ : Fin k → Fin n)
    (κ : Fin k → Fin m) (h : (A.submatrix ρ κ).det ≠ 0) : -- --- CONCL ---
    k ≤ A.rank := by -- --- PROOF ---
  have hu : IsUnit (A.submatrix ρ κ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  have := rank_submatrix_le A ρ κ
  rw [rank_of_isUnit _ hu, Fintype.card_fin] at this
  exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

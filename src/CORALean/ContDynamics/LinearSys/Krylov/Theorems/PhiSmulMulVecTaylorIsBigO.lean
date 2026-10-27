module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Normed.Operator.Asymptotics

@[expose] public section

/-!
# The Taylor expansion of `φ_j(tN)x` at `t = 0`

`φ_j(tN)x = Σ_{i<q} tⁱ/(i + j)! Nⁱx + O(t^q)` as `t → 0`, `φ_j` the series [1, Eq. 4.1] (4.1a),
the expansion behind (5.6) of [1, Remark 4]. The series `Σ_k zᵏ/(k + j)!` has infinite radius
(ratio `1/(k + j + 1) → 0`), so its sum has it as power series at `0`, and
`φ_j(y) - Σ_{i<q} yⁱ/(i + j)! = O(‖y‖^q)`; at `y = tN`, through `B ↦ Bx`, this is `O(t^q)`.

## Inputs
* `N` – complex matrix
* `x` – vector
* `j` – φ-function index
* `q` – Taylor order

## Hypotheses
* none

## Conclusion
* the φ-function Taylor remainder is of the order of the power near zero

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Asymptotics Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Remark 4]'s step: `φ_j(tN)x - Σ_{i<q} tⁱ/(i + j)! Nⁱx = O(t^q)` as `t → 0`, `φ_j` the
series (4.1a), for a complex matrix `N`. -/
theorem Krylov.phi_smul_mulVec_taylor_isBigO (N : Mat ℂ k k) (x : Fin k → ℂ)
    (j q : ℕ) : -- --- CONCL ---
    (fun t : ℝ => (∑' i : ℕ, ((Nat.factorial (i + j) : ℝ)⁻¹) • (t • N) ^ i) *ᵥ x -
        ∑ i ∈ Finset.range q, ((t ^ i * ((Nat.factorial (i + j) : ℝ)⁻¹) : ℝ)) • (N ^ i *ᵥ x))
      =O[𝓝 0] fun t => t ^ q := by -- --- PROOF ---
  set c : ℕ → ℝ := fun i => ((Nat.factorial (i + j) : ℝ)⁻¹) with hc
  -- infinite radius, by the ratio test
  have hr : (FormalMultilinearSeries.ofScalars (Mat ℂ k k) c).radius = ⊤ := by
    refine FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto _ _
      (Eventually.of_forall fun i => by positivity) ?_
    have h : ∀ i : ℕ, ‖c i.succ‖ / ‖c i‖ = 1 / ((i : ℝ) + j + 1) := fun i => by
      simp only [hc, norm_inv, Real.norm_natCast, Nat.succ_add, Nat.factorial_succ, Nat.cast_mul]
      push_cast
      field_simp
      exact (Real.norm_of_nonneg (by positivity)).symm
    simp only [h]
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
  have hP := ((FormalMultilinearSeries.ofScalars (Mat ℂ k k) c).hasFPowerSeriesOnBall
    (by rw [hr]; exact ENNReal.zero_lt_top)).hasFPowerSeriesAt.isBigO_sub_partialSum_pow q
  have hcN : Tendsto (fun t : ℝ => t • N) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const N
  -- `‖tN‖^q ≤ ‖N‖^q |t|^q`
  have h3 : (fun t : ℝ => ‖t • N‖ ^ q) =O[𝓝 0] fun t => t ^ q := by
    refine IsBigO.of_bound (‖N‖ ^ q) (Eventually.of_forall fun t => ?_)
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (by positivity), norm_pow, mul_comm]
  -- `B ↦ Bx` is continuous linear
  let L : Mat ℂ k k →ₗ[ℝ] (Fin k → ℂ) :=
    { toFun := fun B => B *ᵥ x
      map_add' := fun B C => Matrix.add_mulVec B C x
      map_smul' := fun r B => by rw [Matrix.smul_mulVec, RingHom.id_apply] }
  have h4 := ((LinearMap.toContinuousLinearMap L).isBigO_comp _ (𝓝 0)).trans
    ((hP.comp_tendsto hcN).trans h3)
  refine h4.congr_left fun t => ?_
  show ((FormalMultilinearSeries.ofScalars (Mat ℂ k k) c).sum (0 + t • N) -
    (FormalMultilinearSeries.ofScalars (Mat ℂ k k) c).partialSum q (t • N)) *ᵥ x = _
  rw [zero_add, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars_apply_eq,
    Matrix.sub_mulVec, Matrix.sum_mulVec, smul_pow, smul_smul, hc, Matrix.smul_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

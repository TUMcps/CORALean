module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-!
# The determinant of a positive semidefinite matrix is at most `(tr/n)ⁿ`

AM-GM on the eigenvalues: `det S = ∏ λᵢ ≤ (∑ λᵢ / n)ⁿ = (tr S / n)ⁿ` for `S ⪰ 0` and `n ≥ 1`. It is
what makes `E(nGGᵀ, z̄)` the ellipsoid of least volume around a parallelotope in [1, Sec. III-A
(Remark a)], and `eq_smul_one_of_det_eq_trace_div_pow` is the equality case.

## Inputs
* `S` – matrix

## Hypotheses
* `hS` – the matrix is positive semidefinite
* `hn` – the dimension is positive

## Conclusion
* the determinant is at most the power of the mean eigenvalue given by the trace over the dimension

## References

* [1] [V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". 2020 American Control Conference (ACC),
      2020.](../../../references/2020/gassmann-acc-zonotope-ellipsoid.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `det S ≤ (tr S / n)ⁿ` for positive semidefinite `S`, `n ≥ 1`. -/
theorem det_le_trace_div_pow {S : Mat ℝ n n} (hS : S.PosSemidef) (hn : 0 < n) : -- --- CONCL ---
    S.det ≤ (S.trace / n) ^ n := by -- --- PROOF ---
  have hH := hS.1
  rw [hH.det_eq_prod_eigenvalues, hH.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  set ev := hH.eigenvalues
  have hnn : ∀ i, 0 ≤ ev i := hS.eigenvalues_nonneg
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- the weighted AM-GM with the weights `1/n`
  have hw : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
    simp [Finset.card_univ]; field_simp
  have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (n : ℝ)) ev
    (fun _ _ => by positivity) hw (fun i _ => hnn i)
  have hprod : (∏ i, ev i ^ (1 / (n : ℝ))) ^ n = ∏ i, ev i := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hnn i), one_div_mul_cancel hn'.ne', Real.rpow_one]
  have hsum : ∑ i, 1 / (n : ℝ) * ev i = (∑ i, ev i) / n := by
    rw [← Finset.mul_sum]; ring
  rw [← hprod, ← hsum]
  exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hnn i) _) hgm n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

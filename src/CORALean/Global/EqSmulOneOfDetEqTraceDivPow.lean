import CORALean.Global.Tensor
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities

/-!
# Equality in `det S ≤ (tr S / n)ⁿ`

The equality case of `det_le_trace_div_pow`: AM-GM is an equality only when the eigenvalues
are all equal, and a symmetric matrix with all its eigenvalues `c` is `c I` (the spectral
theorem). It is what makes `E(nGGᵀ, z̄)` the only ellipsoid of least volume around a
parallelotope in [1, Sec. III-A (Remark a)].

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `det S = (tr S / n)ⁿ` for positive semidefinite `S`, `n ≥ 1`, forces `S = (tr S / n) I`. -/
theorem eq_smul_one_of_det_eq_trace_div_pow {S : Mat ℝ n n} (hS : S.PosSemidef) (hn : 0 < n)
    (h : S.det = (S.trace / n) ^ n) : S = (S.trace / n) • (1 : Mat ℝ n n) := by -- --- PROOF ---
  have hH := hS.1
  set ev := hH.eigenvalues with hevdef
  have hnn : ∀ i, 0 ≤ ev i := hS.eigenvalues_nonneg
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdet : S.det = ∏ i, ev i := by
    rw [hH.det_eq_prod_eigenvalues]; simp [ev]
  have htr : S.trace = ∑ i, ev i := by
    rw [hH.trace_eq_sum_eigenvalues]; simp [ev]
  set A : ℝ := S.trace / n with hAdef
  have hA : 0 ≤ A := div_nonneg (by rw [htr]; exact Finset.sum_nonneg fun i _ => hnn i) hn'.le
  -- AM-GM with the weights `1/n` is an equality: `∏ λᵢ^(1/n) = A = ∑ λᵢ/n`
  have hw : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
    simp [Finset.card_univ]; field_simp
  have hgeo : ∏ i, ev i ^ (1 / (n : ℝ)) = ∑ i, 1 / (n : ℝ) * ev i := by
    rw [Real.finsetProd_rpow _ _ (fun i _ => hnn i), ← hdet, h, ← Real.rpow_natCast,
      ← Real.rpow_mul hA, mul_one_div_cancel hn'.ne', Real.rpow_one, hAdef, htr,
      ← Finset.mul_sum]
    ring
  have hall := (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos Finset.univ
    (fun _ => 1 / (n : ℝ)) ev (fun _ _ => by positivity) hw (fun i _ => hnn i)).mp hgeo
  -- so every eigenvalue is their mean `A`
  have hevA : ∀ i, ev i = A := fun i => by
    have hsum : ∑ j, ev j = n * ev i := by
      rw [Finset.sum_congr rfl fun j _ => hall j (Finset.mem_univ _) i (Finset.mem_univ _)]
      simp
    rw [hAdef, htr, hsum]; field_simp
  -- the spectral theorem with a constant diagonal
  have hdiag : diagonal (RCLike.ofReal ∘ ev) = (A • 1 : Mat ℝ n n) := by
    ext i j
    simp [diagonal_apply, hevA, Matrix.one_apply]
  rw [hH.spectral_theorem, ← hevdef, hdiag, map_smul, map_one]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

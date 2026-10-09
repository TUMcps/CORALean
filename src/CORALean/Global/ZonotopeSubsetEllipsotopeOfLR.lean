import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The linear relaxation proves a zonotope lies in an ellipsotope

[1, Thm. 15], the containment half: if `H X = G` and `‖X‖_{L⊤₁,q} ≤ 1` Eq. 29 of [1, Thm. 15],
the `q`-norm of the vector of the rows' absolute sums of `X`, then `Z(G) ⊆ E_q(H)`. A point
`G α = H (X α)` with `‖α‖_∞ ≤ 1` has `|(X α)ᵢ| ≤ Σⱼ |Xᵢⱼ|`, and the `q`-norm is monotone in the
absolute values. The surjectivity of `H` and the accuracy bound of [1, Thm. 15] are not needed
here, and not proved.

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal

variable {m l : ℕ} {W : Type} [AddCommGroup W] [Module ℝ W]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The `q`-norm is monotone in the absolute values of the entries. -/
theorem aux_piLp_norm_le (q : ℝ≥0∞) [Fact (1 ≤ q)] (a b : Fin l → ℝ)
    (h : ∀ i, |a i| ≤ b i) : ‖WithLp.toLp q a‖ ≤ ‖WithLp.toLp q b‖ := by -- --- PROOF ---
  have hb : ∀ i, 0 ≤ b i := fun i => (abs_nonneg _).trans (h i)
  by_cases hq : q = ∞
  · -- the supremum norm: each entry is below the corresponding one
    subst hq
    rcases isEmpty_or_nonempty (Fin l) with hl | hl
    · simp [PiLp.norm_eq_ciSup]
    simp only [PiLp.norm_eq_ciSup, Real.norm_eq_abs]
    refine ciSup_le fun i => (h i).trans ?_
    exact le_ciSup (f := fun i => |b i|) (Set.finite_range _).bddAbove i |>.trans' (by
      rw [abs_of_nonneg (hb i)])
  · -- a finite exponent: the sums of powers compare termwise
    have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
    have hq0 : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq1).ne' hq
    rw [PiLp.norm_eq_sum hq0, PiLp.norm_eq_sum hq0]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity)
      (Finset.sum_le_sum fun i _ => ?_) (by positivity)
    simp only [Real.norm_eq_abs]
    exact Real.rpow_le_rpow (abs_nonneg _) ((h i).trans (le_of_eq (abs_of_nonneg (hb i)).symm))
      hq0.le


-- =======================================  MAIN THEOREM  ======================================= --

theorem zonotope_subset_ellipsotope_of_lr (q : ℝ≥0∞) [Fact (1 ≤ q)] (G : (Fin m → ℝ) →ₗ[ℝ] W)
    (H : PiLp q (fun _ : Fin l => ℝ) →ₗ[ℝ] W) (X : Matrix (Fin l) (Fin m) ℝ)
    (hGX : ∀ α, G α = H (WithLp.toLp q (X.mulVec α)))
    (hX : ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖ ≤ 1) :
    {x | ∃ α : Fin m → ℝ, ‖α‖ ≤ 1 ∧ x = G α} ⊆
      {x | ∃ β : PiLp q (fun _ : Fin l => ℝ), ‖β‖ ≤ 1 ∧ x = H β} := by -- --- PROOF ---
  rintro _ ⟨α, hα, rfl⟩
  refine ⟨WithLp.toLp q (X.mulVec α), ?_, hGX α⟩
  -- each entry of `X α` is below the row's absolute sum, as `|αⱼ| ≤ 1`
  refine le_trans (aux_piLp_norm_le q _ _ fun i => ?_) hX
  rw [Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) ((norm_le_pi_norm α j).trans hα)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

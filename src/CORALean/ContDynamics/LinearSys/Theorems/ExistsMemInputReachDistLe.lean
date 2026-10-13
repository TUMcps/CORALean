import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormMulNormExpIntegralSubLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSubOneSubLeSqMulExp

/-!
# Every point of `□(β_r)` is nearly reached by a constant input

The heart of [1, Lemma 1]'s convergence half: a point `w` with `‖w‖ ≤ β_r =
(e^{r‖A‖} - 1)/‖A‖ · µ` is within `µ‖A‖e^{r‖A‖}r²` of what the constant input
`u = ‖A‖/(e^{r‖A‖} - 1) · w` reaches over `[0, r]`. That input is admissible, `‖u‖ ≤ µ`,
and it reaches `(∫₀ʳ e^{As} ds) u`.

The printed proof splits `x_u - x` into `∫ (e^{(r-s)A} - I) u` and
`(r‖A‖/(e^{r‖A‖} - 1) - 1)(x - e^{rA}z)`; here the same two pieces are bounded by
`(e^{r‖A‖} - 1 - r‖A‖)/‖A‖ · µ` each, through the series of `∫₀ʳ e^{As} ds` rather than
an integral, and `e^x - 1 - x ≤ x²e^x/2` closes it.

`closedBall 0 µ ⊆ U` is what makes the constant input admissible, the paper's
`‖u(t)‖ ≤ µ` read as "every such input is allowed"; `0 < ‖A‖` is its division by `‖A‖`.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1], second half, at one point: `w ∈ □(β_r)` is within `µ‖A‖e^{r‖A‖}r²` of a
point the input reaches over `[0, r]`. -/
theorem LinearSys.exists_mem_inputReach_dist_le (sys : LinearSys 𝕋 n) {U : S n} {μ r : ℝ}
    (hA : 0 < ‖toRealMat sys.A‖) (hr : 0 ≤ r) (hμ : 0 ≤ μ)
    (hU : Metric.closedBall 0 μ ⊆ construct U) {w : Vec ℝ n}
    (hw : ‖w‖ ≤ (Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖ * μ) :
    ∃ v ∈ sys.inputReach U r,
      dist w v ≤ μ * ‖toRealMat sys.A‖ * Real.exp (r * ‖toRealMat sys.A‖)
        * r ^ 2 := by -- --- PROOF ---
  set A := toRealMat sys.A
  set a := ‖A‖
  set x := r * a with hxdef
  have hx0 : 0 ≤ x := mul_nonneg hr hA.le
  have hxE : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  -- the constant input, scaled so that it reaches `w` to first order
  set u : Vec ℝ n := (a / (Real.exp x - 1)) • w with hudef
  have hu : ‖u‖ ≤ μ := by
    rcases (hx0.trans hxE).eq_or_lt with h | h
    · rw [hudef, ← h, div_zero, zero_smul, norm_zero]; exact hμ
    · rw [hudef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hA.le h.le)]
      calc a / (Real.exp x - 1) * ‖w‖ ≤ a / (Real.exp x - 1) * ((Real.exp x - 1) / a * μ) :=
            mul_le_mul_of_nonneg_left hw (div_nonneg hA.le h.le)
        _ = μ := by field_simp
  have huU : u ∈ construct U := hU (mem_closedBall_zero_iff.mpr hu)
  refine ⟨MatExp.expIntegral A r *ᵥ u, sys.expIntegral_mem_inputReach hr huU, ?_⟩
  -- first piece: the integrated exponential against `r I`
  have hM : ‖MatExp.expIntegral A r - r • (1 : Mat ℝ n n)‖ ≤ (Real.exp x - 1 - x) / a := by
    rw [le_div_iff₀ hA, mul_comm]
    exact MatExp.norm_mul_norm_expIntegral_sub_le A hr
  have h1 : ‖r • u - MatExp.expIntegral A r *ᵥ u‖ ≤ (Real.exp x - 1 - x) / a * μ := by
    have heq : r • u - MatExp.expIntegral A r *ᵥ u
        = -((MatExp.expIntegral A r - r • (1 : Mat ℝ n n)) *ᵥ u) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]; abel
    rw [heq, norm_neg]
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul hM hu (norm_nonneg _) (div_nonneg (by linarith) hA.le))
  -- second piece: `w` against `r u`, a multiple `1 - x/(e^x - 1)` of `w`
  have h2 : ‖w - r • u‖ ≤ (Real.exp x - 1 - x) / a * μ := by
    rcases (hx0.trans hxE).eq_or_lt with h | h
    · have hw0 : w = 0 := norm_le_zero_iff.mp (by rw [← h, zero_div, zero_mul] at hw; exact hw)
      rw [hudef, hw0, smul_zero, smul_zero, sub_zero, norm_zero]
      exact mul_nonneg (div_nonneg (by linarith) hA.le) hμ
    · have heq : w - r • u = (1 - x / (Real.exp x - 1)) • w := by
        rw [hudef, smul_smul, sub_smul, one_smul, hxdef, mul_div_assoc]
      have hc : 0 ≤ 1 - x / (Real.exp x - 1) := by
        rw [sub_nonneg, div_le_one h]; exact hxE
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      calc (1 - x / (Real.exp x - 1)) * ‖w‖
          ≤ (1 - x / (Real.exp x - 1)) * ((Real.exp x - 1) / a * μ) :=
            mul_le_mul_of_nonneg_left hw hc
        _ = (Real.exp x - 1 - x) / a * μ := by field_simp
  -- the two pieces, and `e^x - 1 - x ≤ x²e^x/2`
  have h3 : 2 * ((Real.exp x - 1 - x) / a * μ) ≤ μ * a * Real.exp x * r ^ 2 := by
    have hq := exp_sub_one_sub_le_sq_mul_exp hx0
    have : 2 * ((Real.exp x - 1 - x) / a * μ) ≤ 2 * (x ^ 2 / 2 * Real.exp x / a * μ) := by
      gcongr
    refine this.trans (le_of_eq ?_)
    rw [hxdef]; field_simp
  rw [dist_eq_norm]
  calc ‖w - MatExp.expIntegral A r *ᵥ u‖
      ≤ ‖w - r • u‖ + ‖r • u - MatExp.expIntegral A r *ᵥ u‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ((Real.exp x - 1 - x) / a * μ) := by linarith
    _ ≤ μ * a * Real.exp x * r ^ 2 := h3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

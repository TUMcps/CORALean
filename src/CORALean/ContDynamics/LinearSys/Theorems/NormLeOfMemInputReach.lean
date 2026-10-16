module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulLe
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# How far the input alone reaches

eq. 3 of [1]: every point an input bounded by `μ` drives the state to over `[0, τ]`, from the
origin, has sup norm at most `β_τ = (e^{τ‖A‖} - 1)/‖A‖ · μ`, the radius [1, Lemma 1] bloats
by. Pointwise `‖e^{A(τ-s)} u(s)‖ ≤ e^{(τ-s)‖A‖} μ`, and that bound integrates to `β_τ`.

`0 < ‖A‖` is [1]'s own, implicit in dividing by `‖A‖`: at `A = 0` the right side reads
Lean's `0 / 0 = 0` while the input still reaches `τ μ`.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `∫₀^τ e^{(τ-s)a} μ ds = (e^{τa} - 1)/a · μ`, by the fundamental theorem of calculus. -/
theorem aux_integral_exp_sub_mul {a τ : ℝ} (ha : 0 < a) (μ : ℝ) :
    ∫ s in (0:ℝ)..τ, Real.exp ((τ - s) * a) * μ
      = (Real.exp (τ * a) - 1) / a * μ := by -- --- PROOF ---
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) τ,
      HasDerivAt (fun s => -(Real.exp ((τ - s) * a) / a * μ)) (Real.exp ((τ - s) * a) * μ) s := by
    intro s _
    have h1 : HasDerivAt (fun s => (τ - s) * a) (-a) s := by
      simpa using ((hasDerivAt_id s).const_sub τ).mul_const a
    have h2 : HasDerivAt (fun s => -(Real.exp ((τ - s) * a) / a * μ))
        (-(Real.exp ((τ - s) * a) * -a / a * μ)) s := ((h1.exp.div_const a).mul_const μ).neg
    have h3 : -(Real.exp ((τ - s) * a) * -a / a * μ) = Real.exp ((τ - s) * a) * μ := by
      field_simp
    rwa [h3] at h2
  rw [integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun s => Real.exp ((τ - s) * a) * μ).intervalIntegrable _ _)]
  simp only [sub_zero, sub_self, zero_mul, Real.exp_zero]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- eq. 3 of [1]: an input bounded by `μ` reaches no further than `(e^{τ‖A‖} - 1)/‖A‖ · μ`. -/
theorem LinearSys.norm_le_of_mem_inputReach (sys : LinearSys 𝕋 n) {U : S n} {μ τ : ℝ}
    (hA : 0 < ‖toRealMat sys.A‖) (hτ : 0 ≤ τ) (hU : ∀ u ∈ construct U, ‖u‖ ≤ μ)
    {v : Vec ℝ n} (hv : v ∈ sys.inputReach U τ) :
    ‖v‖ ≤ (Real.exp (τ * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖ * μ := by -- --- PROOF ---
  obtain ⟨u, hu, -, rfl⟩ := hv
  set a := ‖toRealMat sys.A‖
  rw [← aux_integral_exp_sub_mul hA μ]
  refine norm_integral_le_of_norm_le hτ (Filter.Eventually.of_forall fun s hs => ?_)
    ((by fun_prop : Continuous fun s => Real.exp ((τ - s) * a) * μ).intervalIntegrable _ _)
  -- pointwise: the propagator's norm times the input's
  have hs' : s ∈ Set.Icc (0:ℝ) τ := ⟨hs.1.le, hs.2⟩
  calc ‖exp ((τ - s) • toRealMat sys.A) *ᵥ u s‖
      ≤ ‖exp ((τ - s) • toRealMat sys.A)‖ * ‖u s‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ Real.exp ((τ - s) * a) * μ :=
        mul_le_mul (MatExp.norm_exp_smul_le _ (by linarith [hs.2])) (hU _ (hu s hs'))
          (norm_nonneg _) (Real.exp_nonneg _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

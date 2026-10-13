module

public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.MulVecL

@[expose] public section

/-!
# The exponential integral over a joined window

`∫₀^{a+b} e^{Aσ}dσ v = e^{Ab} ∫₀ᵃ e^{Aσ}dσ v + ∫₀ᵇ e^{Aσ}dσ v`: the window
`[0, a + b]` is `[0, b]` followed by `[b, b + a]`, and on the second piece
`e^{Aσ} = e^{Ab} e^{A(σ - b)}`. What a constant input contributes by
`t = t_k + τ` is therefore what it contributes by `τ`, carried across `t_k`,
plus what it contributed by `t_k` — the recursion a windowed reach set of a
constant input runs on.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `expIntegral` over `[0, a + b]`: the part over `[0, a]` carried across `b`,
plus the part over `[0, b]`. -/
theorem Real.MatExp.expIntegral_add_mulVec (A : Mat ℝ n n) (v : Vec ℝ n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.MatExp.expIntegral A (a + b) *ᵥ v
      = exp (b • A) *ᵥ (Real.MatExp.expIntegral A a *ᵥ v)
        + Real.MatExp.expIntegral A b *ᵥ v := by -- --- PROOF ---
  rw [Real.MatExp.expIntegral_mulVec A v (add_nonneg ha hb),
    Real.MatExp.expIntegral_mulVec A v ha, Real.MatExp.expIntegral_mulVec A v hb]
  have hcont : Continuous fun σ : ℝ => exp (σ • A) *ᵥ v :=
    (mulVecL.continuous.comp (exp_continuous.comp (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  -- `[0, a + b]` is `[0, b]` followed by `[b, a + b]`
  have hsplit : (∫ σ in (0:ℝ)..(a + b), exp (σ • A) *ᵥ v)
      = (∫ σ in (0:ℝ)..b, exp (σ • A) *ᵥ v) + ∫ σ in b..(a + b), exp (σ • A) *ᵥ v :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 b)
      (hcont.intervalIntegrable b (a + b))).symm
  -- the second piece, shifted back to start at zero, with `e^{Ab}` pulled out
  have hsecond : (∫ σ in b..(a + b), exp (σ • A) *ᵥ v)
      = exp (b • A) *ᵥ ∫ σ in (0:ℝ)..a, exp (σ • A) *ᵥ v := by
    have hshift := intervalIntegral.integral_comp_add_right
      (a := (0:ℝ)) (b := a) (fun σ : ℝ => exp (σ • A) *ᵥ v) b
    rw [zero_add] at hshift
    rw [← hshift]
    have hcomm : (∫ σ in (0:ℝ)..a, mulVecL (exp (b • A)) (exp (σ • A) *ᵥ v))
        = exp (b • A) *ᵥ ∫ σ in (0:ℝ)..a, exp (σ • A) *ᵥ v :=
      ContinuousLinearMap.intervalIntegral_comp_comm _ (hcont.intervalIntegrable 0 a)
    rw [← hcomm]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    have hc : Commute (b • A) (σ • A) := ((Commute.refl A).smul_left b).smul_right σ
    show exp ((σ + b) • A) *ᵥ v = exp (b • A) *ᵥ (exp (σ • A) *ᵥ v)
    have h := exp_add_of_commute hc
    rw [show (σ + b) • A = b • A + σ • A by rw [add_smul, add_comm], Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ v) h
  rw [hsplit, hsecond, add_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# The defect-based integral representation of the Krylov error

[1, Eq. 2.8]: the error `L_m(t)v` and the defect `D_m(t)v` satisfy
`L_m'(t)v = σAL_m(t)v + D_m(t)v`, `L_m(0)v = 0`, whence `L_m(t)v = ∫₀ᵗ E(t - s)D_m(s)v ds`,
`E(t) = e^{σtA}`. Stated for any `y` with `y' = My + D`, `y(0) = 0` and continuous `D`, with
`M = σA`: `e^{(t-s)M}y(s)` has derivative `e^{(t-s)M}D(s)`, and the fundamental theorem of
calculus gives the identity.

## Inputs
* `M` – matrix
* `y` – error function
* `D` – defect function
* `t` – time

## Hypotheses
* `hy0` – error vanishes at zero
* `hy` – error solves the defect equation
* `hD` – defect continuous

## Conclusion
* the error equals the integral of the propagated defect

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 2.8]: `y' = My + D`, `y(0) = 0` give `y(t) = ∫₀ᵗ e^{(t-s)M}D(s) ds`; [1] takes
`M = σA`, `y = L_m(·)v` and `D = D_m(·)v`. -/
theorem Krylov.error_eq_integral_defect (M : Mat ℂ n n) (y D : ℝ → Fin n → ℂ) (hy0 : y 0 = 0)
    (hy : ∀ s, HasDerivAt y (M *ᵥ y s + D s) s) (hD : Continuous D) (t : ℝ) : -- --- CONCL ---
    y t = ∫ s in (0 : ℝ)..t, exp ((t - s) • M) *ᵥ D s := by -- --- PROOF ---
  -- `B ↦ (x ↦ Bx)`, continuous and ℝ-linear, for the product rule
  let Φ : Mat ℂ n n →L[ℝ] ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun B => LinearMap.toContinuousLinearMap ((Matrix.mulVecLin B).restrictScalars ℝ)
        map_add' := by intro B C; ext v i; simp
        map_smul' := by intro c B; ext v i; simp }
  -- `g(s) = e^{(t-s)M}y(s)` has derivative `e^{(t-s)M}D(s)`, `M` commuting with `e^{(t-s)M}`
  have hg : ∀ s, HasDerivAt (fun s => exp ((t - s) • M) *ᵥ y s)
      (exp ((t - s) • M) *ᵥ D s) s := by
    intro s
    have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) M (t - s)).scomp s
      ((hasDerivAt_id s).const_sub t)
    have hC : HasDerivAt (fun r : ℝ => Φ (exp ((t - r) • M)))
        (Φ ((-1 : ℝ) • (M * exp ((t - s) • M)))) s :=
      Φ.hasFDerivAt.comp_hasDerivAt s h
    have h3 : HasDerivAt (fun s => exp ((t - s) • M) *ᵥ y s)
        (((-1 : ℝ) • (M * exp ((t - s) • M))) *ᵥ y s + exp ((t - s) • M) *ᵥ (M *ᵥ y s + D s)) s :=
      hC.clm_apply (hy s)
    refine h3.congr_deriv ?_
    have hc : Commute M (exp ((t - s) • M)) := ((Commute.refl M).smul_right _).exp_right
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← hc.eq, neg_one_smul, Matrix.neg_mulVec,
      ← Matrix.mulVec_mulVec]
    abel
  have hcont : Continuous fun s => exp ((t - s) • M) *ᵥ D s :=
    (exp_continuous.comp ((continuous_const.sub continuous_id).smul continuous_const)).matrix_mulVec
      hD
  -- the fundamental theorem of calculus, `g(0) = e^{tM}y(0) = 0`
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun s _ => hg s) (hcont.intervalIntegrable _ _)
  rw [hftc]
  simp [hy0]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

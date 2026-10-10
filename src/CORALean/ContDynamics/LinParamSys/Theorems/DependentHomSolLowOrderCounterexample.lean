import CORALean.ContDynamics.LinParamSys.Operations.DependentHomSolLowOrder
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# CORA's dependent low-order solution misses the solution's second order

`priv_dependentHomSol` (`LinParamSys.dependentHomSolLowOrder`) keeps, of the input's
`A r²/2 u` term, only the parts with one parameter: the products `A_g⁽ⁱ⁾ U_G⁽ʲ⁾ r²/2` of the
matrix's and the input's parameter terms (the coefficient of `pᵢpⱼ`) are missing, the
`pᵢ²` coefficient of `A² r³/6 U_c` is printed as `A_g⁽ⁱ⁾ r³/6 U_c` rather than with
`(A_g⁽ⁱ⁾)²`, and the third-order products in `p` are dropped. They are of time order two
and three, which the high-order mapping matrices (orders three and four up) do not hold.

The counterexample: `A = p₁ N`, `N` the nilpotent shift, `u = p₁ e₂`, a second parameter with
zero generators (so that CORA takes `expmMixed` rather than `expmOneParam`), `x(0) = 0`. At
`p₁ = 1`, `x(t) = (t²/2, t)`; every point of `R_lowOrder` has first coordinate `0`, so
`x(r)` is in `R_lowOrder ⊕ Z` for no `Z` whose first coordinates stay below `r²/2` in
absolute value. CORA's remaining terms at this system (the high-order mapping matrices, all
products with `N² = 0` or with the zero vector, and `E r` times the input) are of size
`O(r^(η+2))`, read from the source, not run.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix
open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `A = p₁ N`, `u = p₁ e₂`, `p = (1, 0)`, `x(0) = 0`, the solution `x(t) = (t²/2, t)` has
`x(r) ∉ R_lowOrder ⊕ Z` for every `Z` whose first coordinates stay within `δ < r²/2`. -/
theorem LinParamSys.dependentHomSolLowOrder_counterexample {r δ : ℝ} (hδ : δ < r ^ 2 / 2)
    {Z : Set (Vec ℝ 2)} (hZ : ∀ z ∈ Z, |z 0| ≤ δ) :
    let Ag : Fin 2 → Mat ℝ 2 2 := ![!![0, 1; 0, 0], 0]
    let UG : Fin 2 → Vec ℝ 2 := ![![0, 1], 0]
    let p : Fin 2 → ℝ := ![1, 0]
    let x : ℝ → Vec ℝ 2 := fun t => ![t ^ 2 / 2, t]
    x 0 = 0 ∧ (∀ t, HasDerivAt x ((∑ i, p i • Ag i) *ᵥ x t + ∑ i, p i • UG i) t) ∧
      x r ∉ (LinParamSys.dependentHomSolLowOrder 0 Ag 0 0 UG r).construct + Z := by -- --- PROOF ---
  intro Ag UG p x
  refine ⟨?_, ?_, ?_⟩
  -- the start
  · funext i; fin_cases i <;> simp [x]
  -- the flow: `x' = (t, 1) = N x + e₂`
  · intro t
    have hfield : (∑ i, p i • Ag i) *ᵥ x t + ∑ i, p i • UG i = ![t, 1] := by
      funext i; fin_cases i <;> simp [p, Ag, UG, x, Fin.sum_univ_two]
    rw [hfield]
    refine hasDerivAt_pi.mpr fun i => ?_
    fin_cases i
    · show HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t
      have h := (hasDerivAt_pow 2 t).div_const 2
      rw [show ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 = t by norm_num] at h
      exact h
    · show HasDerivAt (fun s : ℝ => s) 1 t
      exact hasDerivAt_id' t
  -- every point of `R_lowOrder` has first coordinate `0`
  · rintro ⟨a, ⟨β, -, rfl⟩, z, hz, hxr⟩
    have hG : ∀ l, (LinParamSys.dependentHomSolLowOrder 0 Ag 0 0 UG r).G l 0 = 0 := by
      intro l
      induction l using Fin.addCases with
      | left l =>
        induction l using Fin.addCases with
        -- first order: `M U_G⁽ⁱ⁾ = r U_G⁽ⁱ⁾`, along `e₂` or zero
        | left l =>
          simp only [LinParamSys.dependentHomSolLowOrder, Fin.append_left]
          fin_cases l <;> simp [Ag, UG, Matrix.mulVec, dotProduct]
        -- the squares and the mixed pairs: every product meets `c = U_c = 0` or `A_c = 0`
        | right l =>
          simp only [LinParamSys.dependentHomSolLowOrder, Fin.append_left, Fin.append_right]
          fin_cases l <;> simp [Ag, UG]
      | right l =>
        simp only [LinParamSys.dependentHomSolLowOrder, Fin.append_right]
        split_ifs <;> simp [Ag, UG]
    have hc : (LinParamSys.dependentHomSolLowOrder 0 Ag 0 0 UG r).c 0 = 0 := by
      simp [LinParamSys.dependentHomSolLowOrder, Ag, UG]
    have h0 := congrFun hxr 0
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, hG, hc, smul_eq_mul, mul_zero,
      Finset.sum_const_zero, zero_add] at h0
    have hx0 : x r 0 = r ^ 2 / 2 := by simp [x]
    have := hZ z hz
    rw [h0, hx0] at this
    linarith [le_abs_self (r ^ 2 / 2)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

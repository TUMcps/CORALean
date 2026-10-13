import CORALean.HybridDynamics.Definitions.ResetTaylor
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# [1, Eq. 14] with one `ξ` for all coordinates fails

The reset `r(x) = [x₁² - x₁, x₁³]ᵀ` on the segment `F = [-1, 1] × {0}` (a polynomial zonotope,
centre `c = 0`), expanded to order `γ = 0`: `p(x) = r(0) = 0`, and [1]'s
`L = {∇r(ξ)(x - c) | ξ, x ∈ F} = {s · [2ξ₁ - 1, 3ξ₁²]ᵀ | ξ₁, s ∈ [-1, 1]}`. At `x = (1, 0)`,
`r(x) - p(x) = [0, 1]ᵀ`: the first coordinate forces `ξ₁ = ½` (or `s = 0`, which zeroes the
second), and then the second needs `s = 4/3`, outside `[-1, 1]`. Each coordinate has its own
mean-value point (`½` and `1/∛3`), which is `ResetTaylorMem`.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContinuousLinearMap


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The derivative of the example's reset, coordinate by coordinate. -/
theorem aux_fderiv_reset (ξ w : Vec ℝ 2) :
    fderiv ℝ (fun x : Vec ℝ 2 => ![x 0 ^ 2 - x 0, x 0 ^ 3]) ξ w
      = ![(2 * ξ 0 - 1) * w 0, 3 * ξ 0 ^ 2 * w 0] := by -- --- PROOF ---
  let φ : Fin 2 → Vec ℝ 2 → ℝ := ![fun x => x 0 ^ 2 - x 0, fun x => x 0 ^ 3]
  have hr : (fun x : Vec ℝ 2 => ![x 0 ^ 2 - x 0, x 0 ^ 3]) = fun x j => φ j x := by
    funext x j; fin_cases j <;> rfl
  have h0 := ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) ξ).pow 2).sub
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) ξ)
  have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) ξ).pow 3
  have e0 : φ 0 = (fun x : Vec ℝ 2 => x 0 ^ 2) - fun f => f 0 := rfl
  have e1 : φ 1 = fun x : Vec ℝ 2 => x 0 ^ 3 := rfl
  have hd : ∀ j, DifferentiableAt ℝ (φ j) ξ := by
    intro j; fin_cases j
    · show DifferentiableAt ℝ (φ 0) ξ
      rw [e0]; exact h0.differentiableAt
    · show DifferentiableAt ℝ (φ 1) ξ
      rw [e1]; exact h1.differentiableAt
  -- the derivative of a map into `ℝ²` is the pair of its coordinates' derivatives
  rw [hr, fderiv_pi hd]
  funext j
  fin_cases j
  · show fderiv ℝ (φ 0) ξ w = _
    rw [e0, h0.fderiv]
    simp
    ring
  · show fderiv ℝ (φ 1) ξ w = _
    rw [e1, h1.fderiv]
    simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem resetTaylor_printed_counterexample :
    let r : Vec ℝ 2 → Vec ℝ 2 := fun x => ![x 0 ^ 2 - x 0, x 0 ^ 3]
    let F : Set (Vec ℝ 2) := {x | -1 ≤ x 0 ∧ x 0 ≤ 1 ∧ x 1 = 0}
    (0 : Vec ℝ 2) ∈ F ∧
      ∃ x ∈ F, r x - resetTaylorPoly r 0 0 x ∉ resetLagrangeSet r 0 0 F := by -- --- PROOF ---
  intro r F
  refine ⟨by simp [F], ![1, 0], by simp [F], ?_⟩
  rintro ⟨ξ, hξ, x, hx, h⟩
  have hξ' : -1 ≤ ξ 0 ∧ ξ 0 ≤ 1 ∧ ξ 1 = 0 := hξ
  have hx' : -1 ≤ x 0 ∧ x 0 ≤ 1 ∧ x 1 = 0 := hx
  rw [iteratedFDeriv_one_apply, sub_zero, aux_fderiv_reset] at h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  simp [r, resetTaylorPoly] at e0 e1
  -- the first coordinate forces `ξ₁ = ½` or `x₁ = 0`; either way the second fails
  rcases e0 with h2 | h2
  · have : ξ 0 = 1 / 2 := by linarith
    rw [this] at e1
    nlinarith [hx'.2.1]
  · rw [h2] at e1
    norm_num at e1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

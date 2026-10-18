module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Local `C F⁻¹` blocks miss the coupling of the linearization error

[1, Sec. V-B] evaluates the Lagrange remainder per subsystem, the neighbours' variables inputs,
and joins the parts as in [1, Eq. 15]. The error of the dynamics is `ℓᵈ - C F⁻¹ ℓᵃ`
([1, Eq. 8], [1, Eq. 10]) with the `F⁻¹` of the full system; where the constraints couple the
subsystems, `F` is not block diagonal and a subsystem's `C⁽ⁱ⁾F⁽ⁱ⁾⁻¹` is not its block of `C F⁻¹`.

`f(x, y) = y`, `g(x, y) = (y₁ - y₂, y₂ - x₂²)` about `0`, subsystem 1 = `(x₁, y₁)` with input
`y₂`, subsystem 2 = `(x₂, y₂)`. `C = I`, `D = 0`, `F = [[1, -1], [0, 1]]`, `F⁻¹ = [[1, 1], [0, 1]]`,
`ℓᵃ = (0, -x₂²)`, `ℓᵈ = 0`. At the consistent points `y = (x₂², x₂²)` the dynamics' error
`f(x, y) - (w + Ã Δx) = y` (`w = 0`, `Ã = 0`) is `ℓᵈ - C F⁻¹ ℓᵃ = (x₂², x₂²)`. Subsystem 1
has `C₁ = F₁ = 1` and linear rows `f₁ = y₁`, `g₁ = y₁ - y₂`, so its local error is `0` at every
point while the true error of `ẋ₁` is `1` at `x₂ = 1`: the product of the local sets misses it.
CORA's `priv_linError_mixed_noInt_comp` computes the local one (`Csub * pinv(Fsub)`).

## References

* [1] M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets".
      IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. V-B]: `F⁻¹ F = I`; at the consistent point `x₂ = 1`, `y = (1, 1)` the error of `ẋ₁`
is `1` by `ℓᵈ - C F⁻¹ ℓᵃ`, and equals the dynamics' value `f₁ = y₁` there; the local error of
subsystem 1 is `0` at every point. -/
theorem NonlinDASys.compositional_local_error_counterexample : -- --- STMT ---
    let F : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 0, 1]
    let F_inv : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]
    let g : (Fin 2 → ℝ) → (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x y => ![y 0 - y 1, y 1 - x 1 ^ 2]
    -- the remainder of the constraint about `0`: `g(z) - g(0) - F y` (`D = 0`)
    let ℓa : (Fin 2 → ℝ) → (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x y => g x y - F *ᵥ y
    F_inv * F = 1 ∧
    (∀ x y, ℓa x y = ![0, -(x 1) ^ 2]) ∧
    -- consistent point: `g = 0`, and the full system's error `ℓᵈ - C F⁻¹ ℓᵃ` is `f = y` there
    (g ![0, 1] ![1, 1] = 0 ∧ (0 : Fin 2 → ℝ) - F_inv *ᵥ ℓa ![0, 1] ![1, 1] = ![1, 1]) ∧
    -- subsystem 1 alone: `ℓᵈ₁ = 0`, `ℓᵃ₁ = (y₁ - y₂) - (y₁ - y₂) = 0`, `C₁ F₁⁻¹ = 1`
    (∀ y₁ y₂ : ℝ, (0 : ℝ) - 1 * ((y₁ - y₂) - (1 * y₁ + (-1) * y₂)) = 0) := by -- --- PROOF ---
  intro F F_inv g ℓa
  refine ⟨?_, fun x y => ?_, ⟨?_, ?_⟩, fun y₁ y₂ => by ring⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [F, F_inv, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i; fin_cases i
    · simp [ℓa, g, F, dotProduct, Fin.sum_univ_two]
      ring
    · simp [ℓa, g, F, dotProduct, Fin.sum_univ_two]
  · ext i; fin_cases i <;> simp [g]
  · ext i; fin_cases i <;> simp [ℓa, g, F, F_inv, dotProduct, Fin.sum_univ_two]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

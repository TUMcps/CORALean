module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Module.Pi

@[expose] public section

/-!
# A set with two points is no hyperplane of the line

In one dimension a hyperplane `{x | f x = c}` with `f ≠ 0` is a single point. So a set holding two
different points is none. Used by the `representsa_(S, 'hyperplane')` counterexamples of the classes
whose test is `n == 1`.

## Inputs
* `S` – set of points of the line
* `x` – first point
* `y` – second point

## Hypotheses
* `hx` – the first point is in the set
* `hy` – the second point is in the set
* `hxy` – the two points are different

## Conclusion
* the set is no hyperplane
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A set of the line `ℝ¹ = Fin 1 → ℝ` with two different points is no hyperplane. -/
theorem not_hyperplane_of_two_points_fin1 {S : Set (Fin 1 → ℝ)} {x y : Fin 1 → ℝ} (hx : x ∈ S)
    (hy : y ∈ S) (hxy : x ≠ y) :
    ¬ ∃ (f : (Fin 1 → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ S = {z | f z = c} := by -- --- PROOF ---
  rintro ⟨f, c, hf, rfl⟩
  have key : ∀ z : Fin 1 → ℝ, f z = z 0 * f (fun _ => 1) := fun z => by
    have : z = z 0 • (fun _ : Fin 1 => (1 : ℝ)) := by
      ext i; fin_cases i; simp
    conv_lhs => rw [this]
    rw [map_smul, smul_eq_mul]
  have h1 : x 0 * f (fun _ => 1) = y 0 * f (fun _ => 1) := by
    rw [← key, ← key]; exact hx.trans hy.symm
  have hne : x 0 ≠ y 0 := fun h => hxy (by ext i; fin_cases i; exact h)
  have h0 : f (fun _ => 1) = 0 := by
    by_contra h
    exact hne (mul_right_cancel₀ h h1)
  apply hf
  ext z
  rw [key, h0]; simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

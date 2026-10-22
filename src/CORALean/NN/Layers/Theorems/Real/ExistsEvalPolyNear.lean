module

public import CORALean.NN.Layers.Theorems.Real.Basic
public import Mathlib.Topology.ContinuousMap.Weierstrass

@[expose] public section

/-!
# Weierstrass, in the form a fit is handed in

ℝ-only, as `evalPoly` is: an order and coefficients whose polynomial is within `ε` of `σ`
everywhere on the box.

## Inputs
* `σ` – continuous function
* `l` – lower end of the interval
* `u` – upper end of the interval
* `ε` – accuracy

## Hypotheses
* `hcont` – the function is continuous on the interval
* `hε` – accuracy is positive

## Conclusion
* some polynomial is within the accuracy of the function on the interval
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n : ℕ}

/-- ℝ-only, as `evalPoly` is: coefficients indexed by degree, up to the natural degree. -/
theorem aux_evalPoly_coeff (p : Polynomial ℝ) (t : ℝ) :
    evalPoly (fun i : Fin (p.natDegree + 1) => p.coeff (i : ℕ)) t = Polynomial.eval t p := by
  rw [Polynomial.eval_eq_sum_range]
  exact Fin.sum_univ_eq_sum_range (fun i => p.coeff i * t ^ i) (p.natDegree + 1)

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_evalPoly_near {σ : ℝ → ℝ} {l u ε : ℝ} (hcont : ContinuousOn σ (Set.Icc l u))
    (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ), ∀ x, l ≤ x → x ≤ u → |σ x - evalPoly c x| ≤ ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn l u σ hcont ε hε
  refine ⟨p.natDegree, fun i => p.coeff (i : ℕ), fun x hx hx' => ?_⟩
  rw [aux_evalPoly_coeff p x, abs_sub_comm]
  exact le_of_lt (hp x ⟨hx, hx'⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

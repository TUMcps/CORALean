module

public import CORALean.NN.Layers.Theorems.Real.EvalPolyCoeff
public import Mathlib.Topology.ContinuousMap.Weierstrass

@[expose] public section

/-!
# Weierstrass, in the form a fit is handed in

ℝ-only, as `evalPoly` is: an order and coefficients whose polynomial is within `ε` of `σ`
everywhere on the box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_evalPoly_near {σ : ℝ → ℝ} {l u ε : ℝ} (hcont : ContinuousOn σ (Set.Icc l u))
    (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ), ∀ x, l ≤ x → x ≤ u → |σ x - evalPoly c x| ≤ ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn l u σ hcont ε hε
  refine ⟨p.natDegree, fun i => p.coeff (i : ℕ), fun x hx hx' => ?_⟩
  rw [evalPoly_coeff p x, abs_sub_comm]
  exact le_of_lt (hp x ⟨hx, hx'⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

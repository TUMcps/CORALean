module

public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepSubsetConstInputAddError

@[expose] public section

/-!
# What the step's end encloses beyond what it reaches

`timePointStep_outer` run backwards, and the direction an error measure needs:
the computed set is inside the exact one *widened by a ball*, so `ε` bounds the
enclosure's own error and not only a series remainder.

`timePointStep_subset_constInput_add_error` is where the estimate is done, and
it is sharper: it measures against the states a *held* input reaches. This
weakens that set to the whole `inputReach`, which is the shape every outer
statement about a step is stated in, at the cost of a right-hand side that is no
longer known to be closed — so an inner approximation goes through the sharper
form and never this one.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reverse of `timePointStep_outer`: what the step computes stays inside
what it reaches, widened by `timePointStepError`. -/
theorem LinearSys.timePointStep_subset_reach_add_error (sys : LinearSys 𝕋 n) {r : ℝ}
    (hr : 0 < r) (η : ℕ) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (X₀ U : Zonotope (Vec ℝ n)) :
    (sys.timePointStep (S := 𝒵) r η X₀ U).construct
      ⊆ ((fun x₀ => exp (r • toRealMat sys.A) *ᵥ x₀) '' X₀.construct
          + sys.inputReach (S := 𝒵) U r)
        + Metric.closedBall (0 : Vec ℝ n) (sys.timePointStepError r η U) := by -- --- PROOF ---
  intro y hy
  obtain ⟨p, hp, e, he, rfl⟩ :=
    sys.timePointStep_subset_constInput_add_error hr η hε X₀ U hy
  -- the held input is one admissible input among all of them
  obtain ⟨a, ha, _, ⟨v, hv, rfl⟩, rfl⟩ := hp
  exact ⟨a + MatExp.expIntegral (toRealMat sys.A) r *ᵥ v,
    Set.add_mem_add ha (sys.expIntegral_mem_inputReach (S := 𝒵) hr.le hv), e, he, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

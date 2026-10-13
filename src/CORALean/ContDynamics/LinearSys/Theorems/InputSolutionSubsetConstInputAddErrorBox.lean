import CORALean.ContDynamics.LinearSys.Operations.StepErrorBox
import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepSubsetConstInputAddError
import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallSubsetDiagonal
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

/-!
# One step's input enclosure, against a held input and a zonotope error

`timePointStep_subset_constInput_add_error` from the origin: with nothing to
carry, the step is its input enclosure alone, and what it is measured against
is what one held input reaches, `(∫₀^r e^{As} ds) U`. The error ball is then
replaced by `timePointStepErrorBox`, which contains it.

This is the per-step fact a run accumulates. The radius depends on `U` only,
never on the initial set, so the same box is paid at every step of a run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
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

/-- What `inputSolution` encloses stays inside the held-input contribution
`(∫₀^r e^{As} ds) U`, widened by the step's error box. -/
theorem LinearSys.inputSolution_subset_constInput_add_errorBox (sys : LinearSys 𝕋 n)
    {r : ℝ} (hr : 0 < r) (η : ℕ) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (U : Zonotope (Vec ℝ n)) :
    (sys.inputSolution (S := 𝒵) r η U).construct
      ⊆ (Zonotope.mtimes (MatExp.expIntegral (toRealMat sys.A) r) U).construct
        + (sys.timePointStepErrorBox r η U).construct := by -- --- PROOF ---
  intro v hv
  -- from the origin, the step ends at its input enclosure and nowhere else
  have hstep : (0 : Vec ℝ n) + v
      ∈ (sys.timePointStep (S := 𝒵) r η (Zonotope.ofPoint 0) U).construct := by
    rw [show sys.timePointStep (S := 𝒵) r η (Zonotope.ofPoint 0) U
        = (Zonotope.mtimes (exp (r • toRealMat sys.A)) (Zonotope.ofPoint 0)).plus
            (sys.inputSolution (S := 𝒵) r η U) from rfl,
      ← Zonotope.plus_exact, ← Zonotope.mtimes_exact]
    exact Set.add_mem_add ⟨0, Zonotope.mem_ofPoint 0, Matrix.mulVec_zero _⟩ hv
  obtain ⟨_, ⟨_, ⟨x₀, hx₀, rfl⟩, q, hq, rfl⟩, e, he, hsum⟩ :=
    sys.timePointStep_subset_constInput_add_error hr η hε _ U hstep
  rw [Zonotope.mem_ofPoint_iff] at hx₀
  subst hx₀
  -- the held-input point, and the error ball read as its box
  rw [← Zonotope.mtimes_exact]
  refine ⟨q, hq, e, Zonotope.closedBall_subset_diagonal _ he, ?_⟩
  simpa [Matrix.mulVec_zero] using hsum

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

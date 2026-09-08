import CORALean.ContDynamics.LinearSys.StepInner
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepSubsetConstInputAddError
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

/-!
# The first inner approximation of a continuous reachable set here

`reachInner_inner` at a continuous-time step. Every other reachability theorem
about `LinearSys` puts the computed set on the *left* of the inclusion; this
puts it on the right, so what the step computes minus its own error ball is
*contained in* what the step reaches.

The bridge `minkowskiDiff_inner_of_outer` wants the set on the right convex and
closed, and `e^{Ar} X₀ ⊕ inputReach U r` is not known to be either here —
`inputReach` quantifies over every measurable input, and closing it is a
weak-compactness argument this development does not have. So the outer bound
used is the sharper `timePointStep_subset_constInput_add_error`, whose right-hand
side is `e^{Ar} X₀ ⊕ (∫₀^r e^{As} ds) U`: two zonotope images and a sum, hence a
zonotope, hence convex and compact outright. `expIntegral_mem_inputReach` then
weakens the conclusion back to the set the outer statements are about.

Nonemptiness of the error ball is read off the enclosure rather than computed,
so the sign of `timePointStepError` never has to be examined.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The step's end minus its own error ball is *contained in* what the step
reaches. -/
theorem LinearSys.timePointStepInner_inner (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r)
    (η : ℕ) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (X₀ U : Zonotope (Vec ℝ n)) :
    sys.timePointStepInner r η X₀ U
      ⊆ (fun x₀ => exp (r • toRealMat sys.A) *ᵥ x₀) '' X₀.construct
        + sys.inputReach (S := 𝒵) U r := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set E := Metric.closedBall (0 : Vec ℝ n) (sys.timePointStepError r η U) with hE
  have hOuter := sys.timePointStep_subset_constInput_add_error hr η hε X₀ U
  -- the held-input set is a zonotope: two images under `mtimes`, and their sum
  have hY : (fun x₀ => exp (r • A) *ᵥ x₀) '' X₀.construct
        + (fun v => MatExp.expIntegral A r *ᵥ v) '' U.construct
      = ((Zonotope.mtimes (exp (r • A)) X₀).plus
          (Zonotope.mtimes (MatExp.expIntegral A r) U)).construct := by
    rw [Zonotope.mtimes_exact, Zonotope.mtimes_exact, Zonotope.plus_exact]
  -- the error ball holds a point because it encloses the step's own centre
  have hEne : E.Nonempty := by
    obtain ⟨_, _, e, he, _⟩ := hOuter (Zonotope.centre_mem_construct _)
    exact ⟨e, he⟩
  have hinner := minkowskiDiff_inner_of_outer hEne Metric.isBounded_closedBall
    (hY ▸ Zonotope.convex_construct _) (hY ▸ (Zonotope.isCompact_construct _).isClosed) hOuter
  -- and the held input is one admissible input among all of them
  intro y hy
  obtain ⟨a, ha, _, ⟨v, hv, rfl⟩, rfl⟩ := hinner hy
  exact Set.add_mem_add ha (sys.expIntegral_mem_inputReach (S := 𝒵) hr.le hv)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

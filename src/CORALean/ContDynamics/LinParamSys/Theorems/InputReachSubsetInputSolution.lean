module

public import CORALean.ContDynamics.LinParamSys.Theorems.InputSolutionOuter
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableReflectIoc
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.IntervalInputRemainderSet

@[expose] public section

/-!
# `inputSolution` contains everything the input can contribute at one member

`inputSolution_outer` for every admissible input at once, which is the form `inputReach_mono`
composes with. The set of points is `LinearSys.inputReach` at the member `A`: a `'constParam'` run
fixes one matrix over the step, so what the input can reach is the point system's `P^R(τ)` at that
matrix, and the enclosure it lands in is the box's. `inputReach` is stated over `Icc` and
`inputSolution_outer` reads its input on the reflected `Ioc`, joined by
`aestronglyMeasurable_reflect_Ioc` and one endpoint step, as in the point case.
This is [1, Prop. 2] at the time point `r`, in its corrected form.

## Inputs
* `sys` – system
* `r` – step size
* `η` – Taylor order
* `A` – system matrix member
* `U` – input set

## Hypotheses
* `hr` – step positive
* `hε` – order admissible
* `hA` – `A` lies in the matrix set
* `hconv` – input set convex
* `hclosed` – input set closed
* `hbdd` – input set bounded
* `hRconv` – remainder image convex
* `hRclosed` – remainder image closed
* `hRbdd` – remainder image bounded

## Conclusion
* everything the input alone can reach lies in the enclosure

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point the input alone can reach under one member's flow lies in the
enclosure computed from the matrix set. -/
theorem LinParamSys.inputReach_subset_inputSolution (sys : LinParamSys ℐ n)
    {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖(Interval.smul r sys.A).absMax‖ / ((η : ℝ) + 2) < 1)
    {A : Mat ℝ n n} (hA : A ∈ construct sys.A) {U : S n}
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (MatExp.intervalInputRemainderSet sys.A r η U))
    (hRclosed : IsClosed (MatExp.intervalInputRemainderSet sys.A r η U))
    (hRbdd : Bornology.IsBounded (MatExp.intervalInputRemainderSet sys.A r η U)) : -- --- CONCL ---
    (LinearSys.canonical A : LinearSys ℝ n).inputReach U r
      ⊆ construct (sys.inputSolution r η U) := by -- --- PROOF ---
  rintro _ ⟨u, hmem, hmeas, rfl⟩
  -- the point system's matrix is the member itself
  simp only [Scalar.toRealMat_real]
  refine sys.inputSolution_outer hr η hε hA hconv hclosed hbdd hRconv hRclosed hRbdd ?_
    (aestronglyMeasurable_reflect_Ioc hmeas)
  intro σ hσ
  exact hmem _ ⟨by linarith [hσ.2], by linarith [hσ.1]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

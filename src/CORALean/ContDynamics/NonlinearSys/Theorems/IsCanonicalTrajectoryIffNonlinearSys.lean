module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinearEmbedding
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.Global.IntervalIntegrableMulVecAddOfBounded

@[expose] public section

/-!
# A linear system's runs are its embedding's

Split out of `LinearEmbedding.lean` (issue #62): the guarantee about
`nonlinearSys`, kept apart now that a file holds one public declaration.

`IsCanonicalTrajectory` and `NonlinearSys.IsTrajectory` of `nonlinearSys` state the same
integral equation, the field `A x + u` being the canonical form's integrand. They differ in the
regularity they ask: the linear run's input is measurable, the nonlinear run's field is
measurable and integrable. On a convex `T ∋ 0` under a bounded input set the two agree, the
field being the input plus a continuous drift, and bounded on every window from `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- On a convex `T ∋ 0` under a bounded input set, a run of the canonical form is a run of the
field it is. -/
theorem LinearSys.isCanonicalTrajectory_iff_nonlinearSys (sys : LinearSys 𝕋 n) {T : Set ℝ}
    (hTconv : Convex ℝ T) (h0T : (0:ℝ) ∈ T) (R₀ U : S n)
    (hU : Bornology.IsBounded (construct U)) (x u : ℝ → Vec ℝ n) : -- --- CONCL ---
    sys.IsCanonicalTrajectory T R₀ U x u ↔ sys.nonlinearSys.IsTrajectory T R₀ U x u
      (fun t => sys.nonlinearSys.g (x t) (u t)) := by -- --- PROOF ---
  have hTm : MeasurableSet T := hTconv.ordConnected.measurableSet
  have hAx : ∀ {x : ℝ → Vec ℝ n}, ContinuousOn x T →
      AEStronglyMeasurable (fun s => toRealMat sys.A *ᵥ x s) (volume.restrict T) := fun hx =>
    ((mulVecL (toRealMat sys.A)).continuous.comp_continuousOn hx).aestronglyMeasurable hTm
  refine ⟨fun h => ⟨h.init, h.input, (hAx h.cont).add h.meas,
    fun t ht => intervalIntegrable_mulVec_add_of_bounded h.cont ((hAx h.cont).add h.meas)
      h.input hU (hTconv.ordConnected.uIcc_subset h0T ht), h.cont, h.flow, fun _ _ => rfl⟩,
    fun h => ⟨h.init, h.input, ?_, h.cont, h.flow⟩⟩
  have hm : AEStronglyMeasurable (fun s => (toRealMat sys.A *ᵥ x s + u s) - toRealMat sys.A *ᵥ x s)
      (volume.restrict T) := h.meas.sub (hAx h.cont)
  simpa only [add_sub_cancel_left] using hm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

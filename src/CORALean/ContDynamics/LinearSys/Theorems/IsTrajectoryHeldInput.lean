module

public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormContinuousOn
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormFlow
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero
public import CORALean.ContDynamics.LinearSys.Theorems.HeldInputMeasurable

@[expose] public section

/-!
# A held-input run is a run of the system

[1, Sec. 4.2]'s simulated counterexample, as a run: from any `x₀ ∈ R₀`, under any
input held piecewise at values of `U`, `closedForm` is a Carathéodory
`IsTrajectory` on any horizon `[0, t]`. The input is measurable by
`heldInput_measurable`, and `closedForm_flow` and `closedForm_continuousOn` do the
rest, so no derivative is taken at the steps where the input jumps.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: the run from `x₀ ∈ R₀` under inputs of `U` held piecewise is a
`IsTrajectory` on `[0, t]`. -/
theorem LinearSys.isTrajectory_heldInput (sys : LinearSys 𝕋 n) (R₀ U : S n)
    (hU : Bornology.IsBounded (construct U)) {t : ℝ} (ht : 0 ≤ t) (Δt : ℝ) {x₀ : Vec ℝ n}
    (hx₀ : x₀ ∈ construct R₀) {v : ℕ → Vec ℝ n} (hv : ∀ j, v j ∈ construct U) : -- --- CONCL ---
    sys.IsCanonicalTrajectory (Set.Icc 0 t) R₀ U (sys.closedForm x₀ (LinearSys.heldInput Δt v))
      (LinearSys.heldInput Δt v) :=
  let hu : ∀ s ∈ Set.Icc (0:ℝ) t, LinearSys.heldInput Δt v s ∈ construct U := fun _ _ => hv _
  let hmeas := (LinearSys.heldInput_measurable Δt v).aestronglyMeasurable
    (μ := volume.restrict (Set.Icc 0 t))
  ⟨(sys.closedForm_zero x₀ _).symm ▸ hx₀, hu, hmeas,
    sys.closedForm_continuousOn x₀ ht hU hu hmeas,
    fun _ hτ => sys.closedForm_flow x₀ ht hU hu hmeas hτ⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

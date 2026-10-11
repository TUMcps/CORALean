import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableReflectIoc
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The input is measurable, in the reflected form a step needs

What `inputSolution_outer` asks of the input, in the reflected form the
substitution `τ = c - s` leaves behind. The reflected argument sweeps
`[c - r, c)`, so a domain covering the step ending at `c` is what it needs.
`StepInputOuter` is the one caller, matching `stepInput`'s own reflection.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.aestronglyMeasurable_input_reflected {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory T R₀ U x u) {c r : ℝ}
    (hT : Set.Icc (c - r) c ⊆ T) :
    AEStronglyMeasurable (fun τ => u (c - τ)) (volume.restrict (Set.Ioc 0 r)) := by -- --- PROOF ---
  -- translate the window to `[0, r]`, then reflect it about `r`
  have hpre : (fun s : ℝ => s + (c - r)) ⁻¹' Set.Icc (c - r) c = Set.Icc 0 r := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> exact fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  have hmp : MeasurePreserving (fun s : ℝ => s + (c - r))
      (volume.restrict (Set.Icc 0 r)) (volume.restrict (Set.Icc (c - r) c)) := by
    rw [← hpre]
    exact (measurePreserving_add_right volume (c - r)).restrict_preimage measurableSet_Icc
  have h := aestronglyMeasurable_reflect_Ioc
    ((traj.aestronglyMeasurable_input hT).comp_measurePreserving hmp)
  simpa only [Function.comp_def, show ∀ σ : ℝ, r - σ + (c - r) = c - σ from fun σ => by ring]
    using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

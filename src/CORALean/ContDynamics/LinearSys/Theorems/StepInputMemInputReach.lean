module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Operations.StepInput
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.StepInputEqShifted

@[expose] public section

/-!
# What a step's input contributed is one admissible input's contribution

Step `k`, shifted to start at zero (`stepInput_eq_shifted`), is the integral
`inputReach U Δt` collects, at the input `σ ↦ u(kΔt + σ)`: it stays in `U` on
the step and is measurable there, translation preserving Lebesgue measure. So
any enclosure of `inputReach` encloses every step's input, which is how a float
input solution, guaranteed against `inputReach`, becomes a sampled one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Translating by `c` carries `Icc (a-c) (b-c)` onto `Icc a b` and preserves
Lebesgue measure. -/
theorem aux_aestronglyMeasurable_shift {f : ℝ → Vec ℝ n} {a b c : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b))) :
    AEStronglyMeasurable (fun σ => f (c + σ))
      (volume.restrict (Set.Icc (a - c) (b - c))) := by -- --- PROOF ---
  have hpre : (fun σ : ℝ => c + σ) ⁻¹' Set.Icc a b = Set.Icc (a - c) (b - c) := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> exact fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  have hmp : MeasurePreserving (fun σ : ℝ => c + σ)
      (volume.restrict (Set.Icc (a - c) (b - c))) (volume.restrict (Set.Icc a b)) := by
    rw [← hpre]
    exact (measurePreserving_add_left volume c).restrict_preimage measurableSet_Icc
  exact hf.comp_measurePreserving hmp


-- =======================================  MAIN THEOREM  ======================================= --

/-- Step `k`'s input contribution lies in `inputReach U Δt`, the domain covering
that step alone. -/
theorem LinearSys.CanonicalTrajectory.stepInput_mem_inputReach {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.CanonicalTrajectory T R₀ U x u) (k : ℕ)
    (hT : Set.Icc ((k : ℝ) * Δt) (((k : ℝ) + 1) * Δt) ⊆ T) :
    sys.stepInput u Δt k ∈ sys.inputReach U Δt := by -- --- PROOF ---
  rw [show ((k : ℝ) + 1) * Δt = (k : ℝ) * Δt + Δt from by ring] at hT
  refine ⟨fun σ => u ((k : ℝ) * Δt + σ), fun σ hσ => traj.input _ (hT ⟨?_, ?_⟩), ?_,
    sys.stepInput_eq_shifted u Δt k⟩
  · linarith [hσ.1]
  · linarith [hσ.2]
  -- measurable on the step, then translated back to `[0, Δt]`
  have h := aux_aestronglyMeasurable_shift (c := (k : ℝ) * Δt)
    (traj.aestronglyMeasurable_input hT)
  simpa using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

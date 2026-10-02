import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.Interval.Real.Theorems.ExistsMeasurableMulVecEq
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.Order.ProjIcc

/-!
# A time-varying run is driven by a measurable member of the box

`Trajectory` asks nothing of `t ↦ A t` beyond `A t ∈ sys.A`, and only `A t x(t)`
enters the flow, so a run's parameter can be as wild as a choice per instant.
For an input-free run over `[0, t)` it can be replaced by a measurable one
driving the same flow: at every instant, a member of the box that maps `x(s)`
to the same velocity, chosen by a formula rather than by choice.

The member is `Interval.exists_measurable_mulVec_eq`'s, against the state
extended past the window and the velocity as a one-sided derivative, which every
function has measurably (`stronglyMeasurable_derivWithin_Ici`).

With an input the target is the velocity minus `u(s)`, which `Trajectory` does not
make measurable; `exists_measurable_param_of_measurable` asks that of `u`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   02-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet MeasureTheory

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An input-free run over `[0, t)` is driven by a measurable member of the box:
the same velocity at every instant, from a parameter measurable entry by entry. -/
theorem LinParamSys.Trajectory.exists_measurable_param {sys : LinParamSys ℐ n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n} (traj : sys.Trajectory T R₀ U x u A)
    {t : ℝ} (ht : 0 ≤ t) (hT : Set.Icc 0 t ⊆ T) (hu : ∀ s ∈ Set.Ico 0 t, u s = 0) :
    ∃ Â : ℝ → Mat ℝ n n, (∀ i j, Measurable fun s => Â s i j) ∧
      (∀ s, Â s ∈ construct sys.A) ∧
      ∀ s ∈ Set.Ico 0 t, Â s *ᵥ x s = A s *ᵥ x s := by -- --- PROOF ---
  have h0 : (0:ℝ) ∈ T := hT ⟨le_rfl, ht⟩
  -- the state, extended constantly past the window so that it is continuous everywhere
  have hxc : ContinuousOn x (Set.Icc 0 t) := fun s hs =>
    ((traj.flow s (hT hs)).continuousWithinAt).mono hT
  set y : ℝ → Vec ℝ n := Set.IccExtend ht (Set.restrict (Set.Icc 0 t) x) with hy
  have hyc : Continuous y := (continuousOn_iff_continuous_restrict.mp hxc).Icc_extend'
  have hyx : ∀ s ∈ Set.Icc 0 t, y s = x s := fun s hs => by
    rw [hy, Set.IccExtend_of_mem ht _ hs]; rfl
  -- the velocity, as a one-sided derivative, which is measurable for every function
  set w : ℝ → Vec ℝ n := fun s => derivWithin x (Set.Ici s) s with hw
  have hwm : Measurable w := (stronglyMeasurable_derivWithin_Ici x).measurable
  have hwA : ∀ s ∈ Set.Ico 0 t, w s = A s *ᵥ x s := fun s hs => by
    have hd := (traj.flow s (hT ⟨hs.1, hs.2.le⟩)).mono_of_mem_nhdsWithin
      (mem_nhdsGE_iff_exists_Ico_subset.mpr
        ⟨t, hs.2, fun _ hr => hT ⟨le_trans hs.1 hr.1, hr.2.le⟩⟩)
    rw [hu s hs, add_zero] at hd
    exact hd.derivWithin (uniqueDiffWithinAt_Ici s)
  -- the run's own member puts the velocity between the corner values
  obtain ⟨Â, hm, hB, hÂ⟩ := Interval.exists_measurable_mulVec_eq (traj.param 0 h0)
    hyc.measurable hwm measurableSet_Ico fun s hs => ⟨A s, traj.param s (hT ⟨hs.1, hs.2.le⟩),
      by rw [hyx s ⟨hs.1, hs.2.le⟩, hwA s hs]⟩
  refine ⟨Â, hm, hB, fun s hs => ?_⟩
  rw [← hyx s ⟨hs.1, hs.2.le⟩, hÂ s hs, hwA s hs, hyx s ⟨hs.1, hs.2.le⟩]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

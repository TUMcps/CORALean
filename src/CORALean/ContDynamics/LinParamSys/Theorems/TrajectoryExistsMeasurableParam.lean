module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# A time-varying run is driven by a measurable member of the box everywhere

`Trajectory.measParam` makes `t ↦ A t` measurable on `T`, almost everywhere and
only there; the Peano–Baker expansion (`MatExp.norm_sub_peanoBakerSum_le`) wants a
parameter measurable everywhere and inside the box at every instant. This
supplies one equal to `A` almost everywhere on the window, so the flow, an
integral, cannot tell the two apart.

Each entry is replaced by a measurable representative, the box membership is a
measurable condition on those, and where it fails — a null set inside the window,
the run's own `A` lying in the box there — the member `A 0` stands in.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet MeasureTheory

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run over `[0, t]` agrees almost everywhere there with a parameter that is
measurable and inside the box at every instant. -/
theorem LinParamSys.Trajectory.exists_measurable_param {sys : LinParamSys ℐ n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n} (traj : sys.Trajectory T R₀ U x u A)
    {t : ℝ} (ht : 0 ≤ t) (hT : Set.Icc 0 t ⊆ T) :
    ∃ Â : ℝ → Mat ℝ n n, (∀ i j, Measurable fun s => Â s i j) ∧
      (∀ s, Â s ∈ construct sys.A) ∧
      ∀ᵐ s ∂(volume.restrict (Set.Icc 0 t)), Â s = A s := by -- --- PROOF ---
  classical
  have h0 : (0:ℝ) ∈ T := hT ⟨le_rfl, ht⟩
  have hA : AEStronglyMeasurable A (volume.restrict (Set.Icc 0 t)) :=
    traj.measParam.mono_measure (Measure.restrict_mono hT le_rfl)
  -- every entry, and a measurable representative of it
  have hAij : ∀ i j, AEStronglyMeasurable (fun s => A s i j)
      (volume.restrict (Set.Icc 0 t)) :=
    fun i j => (continuous_id.matrix_elem i j).comp_aestronglyMeasurable hA
  set G : ℝ → Mat ℝ n n := fun s => Matrix.of fun i j => (hAij i j).mk _ s with hG
  have hGm : ∀ i j, Measurable fun s => G s i j :=
    fun i j => (hAij i j).stronglyMeasurable_mk.measurable
  -- where the representatives lie in the box, a measurable set
  set E : Set ℝ := {s | G s ∈ construct sys.A} with hE
  have hEm : MeasurableSet E := by
    have hEq : E = ⋂ i, ⋂ j,
        ({s | sys.A.inf i j ≤ G s i j} ∩ {s | G s i j ≤ sys.A.sup i j}) := by
      ext s
      simp only [hE, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
      exact Interval.mem_mat_iff
    rw [hEq]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      (measurableSet_le measurable_const (hGm i j)).inter
        (measurableSet_le (hGm i j) measurable_const)
  refine ⟨fun s => if s ∈ E then G s else A 0, fun i j => ?_, fun s => ?_, ?_⟩
  · -- measurable: a measurable choice between a representative and a constant
    have hite : (fun s => (if s ∈ E then G s else A 0) i j)
        = fun s => if s ∈ E then G s i j else A 0 i j :=
      funext fun s => by split_ifs <;> rfl
    rw [hite]
    exact Measurable.ite hEm (hGm i j) measurable_const
  · by_cases hs : s ∈ E
    · show (if s ∈ E then G s else A 0) ∈ construct sys.A
      rw [if_pos hs]; exact hs
    · show (if s ∈ E then G s else A 0) ∈ construct sys.A
      rw [if_neg hs]; exact traj.param 0 h0
  · -- almost every instant of the window has every representative right
    have hall : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 t)),
        ∀ i j, (hAij i j).mk _ s = A s i j := by
      rw [ae_all_iff]; intro i
      rw [ae_all_iff]; intro j
      exact (hAij i j).ae_eq_mk.symm
    filter_upwards [hall, ae_restrict_mem measurableSet_Icc] with s hs hsI
    have hGs : G s = A s := Matrix.ext fun i j => hs i j
    have hsE : s ∈ E := by
      show G s ∈ construct sys.A
      rw [hGs]
      exact traj.param s (hT hsI)
    simp only [if_pos hsE, hGs]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

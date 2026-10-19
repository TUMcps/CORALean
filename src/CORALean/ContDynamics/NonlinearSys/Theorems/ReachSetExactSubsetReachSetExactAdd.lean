module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSetExact
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

/-!
# Runs under a constant input concatenate

A run from a point the flow reaches at `T` is the tail of a run from `X₀` over `[0, T + Δt]`:
the reachable set at `Δt` from what is reached at `T` is reached at `T + Δt`. This is what lets
a step-by-step algorithm start each step from the previous step's set, as [1, Alg. 1] does.

The input is the constant `u₀`, `U = {u₀}`, as in [1]. The concatenated run satisfies the
integral equation piece by piece: up to `T` it is the first run's, after `T` the second run's
added to what the first had reached, the integral split at `T`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   18-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Set MeasureTheory intervalIntegral

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What is reached at `Δt` from points reached at `T` is reached at `T + Δt`, under `u₀`. -/
theorem NonlinearSys.reachSetExact_subset_reachSetExact_add (sys : NonlinearSys n m)
    (X₀ X : Set (Vec ℝ n)) (u₀ : Vec ℝ m) {T Δt : ℝ} (hT : 0 ≤ T) (hΔt : 0 ≤ Δt)
    (hX : X ⊆ sys.reachSetExact (S := 𝒮) (Icc 0 T) X₀ {u₀} T) : -- --- CONCL ---
    sys.reachSetExact (S := 𝒮) (Icc 0 Δt) X {u₀} Δt ⊆
      sys.reachSetExact (S := 𝒮) (Icc 0 (T + Δt)) X₀ {u₀}
        (T + Δt) := by -- --- PROOF ---
  classical
  rintro _ ⟨x₂, u₂, traj₂, rfl⟩
  obtain ⟨x₁, u₁, traj₁, hx₁⟩ := hX traj₂.init
  have hu₁ : ∀ t ∈ Icc 0 T, u₁ t = u₀ := fun t ht => traj₁.input t ht
  have hu₂ : ∀ t ∈ Icc 0 Δt, u₂ t = u₀ := fun t ht => traj₂.input t ht
  -- the concatenated run: `x₁` up to `T`, then `x₂` shifted by `T`
  set g : ℝ → Vec ℝ n := fun t => if t ≤ T then x₁ t else x₂ (-T + t)
  have hg₁ : EqOn g x₁ (Icc 0 T) := fun t ht => if_pos ht.2
  have hg₂ : EqOn g (fun t => x₂ (-T + t)) (Icc T (T + Δt)) := fun t ht => by
    by_cases h : t ≤ T
    · have : t = T := le_antisymm h ht.1
      subst this
      simp only [g, if_pos h, neg_add_cancel]
      exact hx₁
    · exact if_neg h
  -- the integrand of the concatenated run, piece by piece
  set F : ℝ → Vec ℝ n := fun s => sys.f (g s) u₀ with hF
  set F₂ : ℝ → Vec ℝ n := fun s => sys.f (x₂ s) (u₂ s) with hF₂
  have he₁ : EqOn F (fun s => sys.f (x₁ s) (u₁ s)) (Icc 0 T) := fun s hs => by
    simp only [hF, hg₁ hs, hu₁ s hs]
  have he₂ : EqOn F (fun s => F₂ (-T + s)) (Icc T (T + Δt)) := fun s hs => by
    simp only [hF, hF₂, hg₂ hs, hu₂ (-T + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩]
  -- each piece integrable, the tail through the shift by `T`
  have hT₀ : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hI₁ : IntervalIntegrable F volume 0 T :=
    (intervalIntegrable_congr fun s hs => (he₁ (by
      rw [uIoc_of_le hT] at hs; exact ⟨hs.1.le, hs.2⟩)).symm).mp (traj₁.integrable T hT₀)
  have hI₂ : ∀ t ∈ Icc T (T + Δt), IntervalIntegrable F volume T t := fun t ht => by
    have h := (traj₂.integrable (-T + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩).comp_add_left
      (-T)
    simp only [sub_neg_eq_add, zero_add, neg_add_cancel_comm] at h
    refine (intervalIntegrable_congr fun s hs => (he₂ ?_).symm).mp (by simpa [add_comm] using h)
    rw [uIoc_of_le ht.1] at hs
    exact ⟨hs.1.le, hs.2.trans ht.2⟩
  have hsplit : Icc 0 (T + Δt) = Icc 0 T ∪ Icc T (T + Δt) :=
    (Icc_union_Icc_eq_Icc hT (by linarith)).symm
  refine ⟨g, fun _ => u₀, ⟨?_, fun _ _ => rfl, ?_, fun t ht => ?_, ?_, fun t ht => ?_,
    fun _ _ => rfl⟩, ?_⟩
  · show g 0 ∈ X₀
    rw [hg₁ ⟨le_rfl, hT⟩]
    exact traj₁.init
  · -- measurable on each piece, the tail through the shift by `T`
    rw [hsplit, aestronglyMeasurable_union_iff]
    refine ⟨traj₁.meas.congr ((ae_restrict_mem measurableSet_Icc).mono fun s hs => (he₁ hs).symm),
      ?_⟩
    have hmaps : MapsTo (fun s => -T + s) (Icc T (T + Δt)) (Icc 0 Δt) :=
      fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact (traj₂.meas.comp_quasiMeasurePreserving
      ((measurePreserving_add_left volume (-T)).quasiMeasurePreserving.restrict hmaps)).congr
        ((ae_restrict_mem measurableSet_Icc).mono fun s hs => (he₂ hs).symm)
  · -- integrable from `0`, across the junction if need be
    by_cases h : t ≤ T
    · exact hI₁.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hT]; exact ⟨ht.1, h⟩))
    · exact hI₁.trans (hI₂ t ⟨(not_le.mp h).le, ht.2⟩)
  · -- continuous on each closed piece
    rw [hsplit]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact traj₁.cont.congr hg₁
    · exact (traj₂.cont.comp ((continuousOn_const (c := -T)).add continuousOn_id)
        fun s (hs : s ∈ Icc T (T + Δt)) => show -T + s ∈ Icc 0 Δt from
          ⟨by linarith [hs.1], by linarith [hs.2]⟩).congr hg₂
  · -- the integral equation, split at `T` past the junction
    by_cases h : t ≤ T
    · have ht' : t ∈ Icc 0 T := ⟨ht.1, h⟩
      rw [hg₁ ht', hg₁ ⟨le_rfl, hT⟩, traj₁.flow t ht']
      congr 1
      refine integral_congr fun s hs => (he₁ ?_).symm
      rw [uIcc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans h⟩
    · have ht' : t ∈ Icc T (T + Δt) := ⟨(not_le.mp h).le, ht.2⟩
      have hs₂ : -T + t ∈ Icc 0 Δt := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
      -- the second run from where the first reached, and the integral split at `T`
      rw [show g t = x₂ (-T + t) from hg₂ ht', hg₁ ⟨le_rfl, hT⟩, traj₂.flow _ hs₂, ← hx₁,
        traj₁.flow T hT₀, ← integral_add_adjacent_intervals hI₁ (hI₂ t ht'), add_assoc]
      congr 2
      · refine integral_congr fun s hs => (he₁ ?_).symm
        rw [uIcc_of_le hT] at hs
        exact hs
      · rw [integral_congr (g := fun s => F₂ (-T + s)) fun s hs => he₂ (by
          rw [uIcc_of_le ht'.1] at hs; exact ⟨hs.1, hs.2.trans ht'.2⟩),
          integral_comp_add_left F₂ (-T)]
        simp [hF₂]
  · show g (T + Δt) = x₂ Δt
    rw [hg₂ ⟨by linarith, le_rfl⟩]
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

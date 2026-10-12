import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSet
import CORALean.ContDynamics.NonlinearSys.Theorems.Shift
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Runs under a constant input concatenate

A run from a point the flow reaches at `T` is the tail of a run from `X₀` over `[0, T + Δt]`:
the reachable set at `Δt` from what is reached at `T` is reached at `T + Δt`. This is what lets
a step-by-step algorithm start each step from the previous step's set, as [1, Alg. 1] does.

The input is the constant `u₀`, `U = {u₀}`. With inputs that may jump the statement fails for
classical runs, which have to be differentiable at the junction from both sides with the one
input value there; a constant input agrees with itself.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Set

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What is reached at `Δt` from points reached at `T` is reached at `T + Δt`, under `u₀`. -/
theorem NonlinearSys.reachSet_subset_reachSet_add (sys : NonlinearSys n m)
    (X₀ X : Set (Vec ℝ n)) (u₀ : Vec ℝ m) {T Δt : ℝ} (hT : 0 ≤ T) (hΔt : 0 ≤ Δt)
    (hX : X ⊆ sys.reachSet (S := fun k => Set (Vec ℝ k)) (Icc 0 T) X₀ {u₀} T) :
    sys.reachSet (S := fun k => Set (Vec ℝ k)) (Icc 0 Δt) X {u₀} Δt ⊆
      sys.reachSet (S := fun k => Set (Vec ℝ k)) (Icc 0 (T + Δt)) X₀ {u₀}
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
  -- the tail as a run on `[T, T + Δt]`
  have tail := traj₂.shift (t₀ := -T) (T' := Icc T (T + Δt))
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (mem_univ _ : x₂ (-T) ∈ (univ : Set (Vec ℝ n)))
  refine ⟨g, fun _ => u₀, ⟨?_, fun _ _ => rfl, fun t ht => ?_⟩, ?_⟩
  · show g 0 ∈ X₀
    rw [hg₁ ⟨le_rfl, hT⟩]
    exact traj₁.init
  · -- the derivative from each side of the junction, `[0, T]` and `[T, T + Δt]`
    rw [← Icc_union_Icc_eq_Icc hT (by linarith : T ≤ T + Δt)]
    refine HasDerivWithinAt.union ?_ ?_
    · by_cases h : t ≤ T
      · have ht' : t ∈ Icc 0 T := ⟨ht.1, h⟩
        have d := traj₁.flow t ht'
        rw [hu₁ t ht', ← hg₁ ht'] at d
        exact d.congr_of_mem hg₁ ht'
      · refine hasDerivWithinAt_iff_hasFDerivWithinAt.mpr
          (HasFDerivWithinAt.of_notMem_closure ?_)
        rw [closure_Icc]
        exact fun h' => h h'.2
    · -- the tail's derivative, where `t ≥ T`
      by_cases h : T ≤ t
      · have ht' : t ∈ Icc T (T + Δt) := ⟨h, ht.2⟩
        have d := tail.flow t ht'
        have e : g t = x₂ (-T + t) := hg₂ ht'
        rw [hu₂ _ ⟨by linarith, by linarith [ht.2]⟩, ← e] at d
        exact d.congr_of_mem hg₂ ht'
      · refine hasDerivWithinAt_iff_hasFDerivWithinAt.mpr
          (HasFDerivWithinAt.of_notMem_closure ?_)
        rw [closure_Icc]
        exact fun h' => h h'.1
  · show g (T + Δt) = x₂ Δt
    rw [hg₂ ⟨by linarith, le_rfl⟩]
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

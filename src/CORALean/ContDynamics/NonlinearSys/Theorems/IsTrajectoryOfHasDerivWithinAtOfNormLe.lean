module

public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryOfHasDerivWithinAt
public import CORALean.Global.AestronglyMeasurableOfHasDerivWithinAt

@[expose] public section

/-!
# A classical run with a bounded field is a Carathéodory run

`IsTrajectory.of_hasDerivWithinAt` with its integrability discharged: a field bounded along the
run on `T` is integrable on every window from `0`, the derivative being measurable
(`aestronglyMeasurable_of_hasDerivWithinAt`). A run confined to a compact region on which the
field is bounded, or one an abstraction error certifies there, has such a field.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input trajectory
* `C` – field bound

## Hypotheses
* `hTconv` – time set convex
* `h0T` – zero in time set
* `init` – start state in initial set
* `input` – inputs in input set
* `hd` – field is the derivative
* `hC` – field bounded along run

## Conclusion
* the state and input form a trajectory
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet MeasureTheory

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A derivative within a convex `T ∋ 0`, bounded on `[0, t]`, is integrable from `0` to `t`. -/
private theorem aux_intervalIntegrable_of_hasDerivWithinAt {T : Set ℝ} {x g : ℝ → Vec ℝ n} {C : ℝ}
    (hTconv : Convex ℝ T) (h0T : (0:ℝ) ∈ T) (hd : ∀ t ∈ T, HasDerivWithinAt x (g t) T t)
    {t : ℝ} (ht : t ∈ T) (hC : ∀ s ∈ Set.uIcc 0 t, ‖g s‖ ≤ C) : -- --- CONCL ---
    IntervalIntegrable g volume 0 t := by -- --- PROOF ---
  have hsub : Set.uIoc (0:ℝ) t ⊆ T :=
    Set.uIoc_subset_uIcc.trans (hTconv.ordConnected.uIcc_subset h0T ht)
  have hfin : volume (Set.uIoc (0:ℝ) t) < ⊤ := by
    rcases le_total 0 t with h | h
    · rw [Set.uIoc_of_le h]; exact measure_Ioc_lt_top
    · rw [Set.uIoc_of_ge h]; exact measure_Ioc_lt_top
  rw [intervalIntegrable_iff]
  refine ⟨(aestronglyMeasurable_of_hasDerivWithinAt hTconv hd).mono_measure
    (Measure.restrict_mono hsub le_rfl), HasFiniteIntegral.restrict_of_bounded (C := C) hfin ?_⟩
  exact (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun s hs =>
    hC s (Set.uIoc_subset_uIcc hs))


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run with the field as its derivative on a convex `T ∋ 0`, bounded there, is a run. -/
theorem NonlinearSys.IsTrajectory.of_hasDerivWithinAt_of_norm_le {sys : NonlinearSys n m}
    {T : Set ℝ} {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {C : ℝ}
    (hTconv : Convex ℝ T) (h0T : (0:ℝ) ∈ T) (init : x 0 ∈ construct R₀)
    (input : ∀ t ∈ T, u t ∈ construct U)
    (hd : ∀ t ∈ T, HasDerivWithinAt x (sys.f (x t) (u t)) T t)
    (hC : ∀ t ∈ T, ‖sys.f (x t) (u t)‖ ≤ C) :
    sys.IsTrajectory T R₀ U x u (fun t => sys.g (x t) (u t)) :=
  .of_hasDerivWithinAt hTconv h0T init input hd fun _ ht =>
    aux_intervalIntegrable_of_hasDerivWithinAt hTconv h0T hd ht fun s hs =>
      hC s (hTconv.ordConnected.uIcc_subset h0T ht hs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

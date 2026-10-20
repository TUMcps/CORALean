module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# A derivative on a convex set is measurable there

A function with the derivative `g t` within a convex `T` at every point of `T` has, at every
point of `T` short of its greatest one, the right derivative `g t`; so `g` agrees with the
unconditionally measurable right derivative of `x` off at most one point, which is null. This
is what lets a classical solution, whose derivative exists everywhere, be read as a
Carathéodory one, whose integrand must be measurable.

## Inputs
* `T` – convex set of times
* `x` – function with a derivative on `T`
* `g` – its derivative

## Hypotheses
* `hTconv` – `T` is convex
* `hd` – `g t` is the derivative of `x` within `T` at each point of `T`

## Conclusion
* `g` is almost everywhere strongly measurable on `T`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The derivative `g` of `x` within a convex `T`, measurable on `T`. -/
theorem aestronglyMeasurable_of_hasDerivWithinAt {T : Set ℝ} {x g : ℝ → E}
    (hTconv : Convex ℝ T) (hd : ∀ t ∈ T, HasDerivWithinAt x (g t) T t) : -- --- CONCL ---
    AEStronglyMeasurable g (volume.restrict T) := by -- --- PROOF ---
  have hTm : MeasurableSet T := hTconv.ordConnected.measurableSet
  -- `T`'s greatest element, if it has one, is the only point the right derivative misses
  set Tbad : Set ℝ := {b | b ∈ T ∧ IsGreatest T b} with hTbaddef
  have hTbad0 : volume Tbad = 0 :=
    Set.Subsingleton.measure_zero (fun a ha b hb => ha.2.unique hb.2) volume
  have hagree : ∀ s ∈ T \ Tbad, derivWithin x (Set.Ici s) s = g s := by
    rintro s ⟨hsT, hsbad⟩
    obtain ⟨b, hbT, hsb⟩ : ∃ b ∈ T, s < b := by
      by_contra hcon
      exact hsbad ⟨hsT, hsT, fun y hy => not_lt.mp (fun hlt => hcon ⟨y, hy, hlt⟩)⟩
    have hIcc : Set.Icc s b ⊆ T := hTconv.ordConnected.out hsT hbT
    have hIci : HasDerivWithinAt x (g s) (Set.Ici s) s :=
      (hd s hsT).mono_of_mem_nhdsWithin (mem_nhdsGE_iff_exists_Ico_subset.mpr
        ⟨b, hsb, fun _ hy => hIcc ⟨hy.1, hy.2.le⟩⟩)
    exact hIci.derivWithin (uniqueDiffWithinAt_Ici s)
  -- the disagreement set is inside `Tbad`, hence null within `volume.restrict T`
  have heq : (fun s => derivWithin x (Set.Ici s) s) =ᶠ[ae (volume.restrict T)] g := by
    have hsub : {s | ¬ derivWithin x (Set.Ici s) s = g s} ∩ T ⊆ Tbad := by
      rintro s ⟨hne, hsT⟩
      by_contra hbad
      exact hne (hagree s ⟨hsT, hbad⟩)
    have hle : volume.restrict T {s | ¬ derivWithin x (Set.Ici s) s = g s} = 0 := by
      rw [Measure.restrict_apply' hTm]
      exact measure_mono_null hsub hTbad0
    rwa [Filter.EventuallyEq, ae_iff]
  exact (stronglyMeasurable_derivWithin_Ici x).aestronglyMeasurable.congr heq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# A classical solution satisfies the integral equation

A function with the derivative `g t` within a convex `T ∋ 0` at every point of `T`, `g`
integrable from `0` to `t`, is `x 0` plus the integral of `g` from `0` to `t`: the fundamental
theorem of calculus, one-sided inside `T`. It is the bridge from a classical solution, a
derivative at every point, to a Carathéodory one, the integral equation.

## Inputs
* `T` – set of times
* `x` – function with a derivative on the set
* `g` – its derivative
* `t` – end time

## Hypotheses
* `hTconv` – the set is convex
* `h0T` – zero belongs to the set
* `hd` – `g t` is the derivative of `x` within the set at each point
* `ht` – the end time belongs to the set
* `hint` – `g` is integrable from zero to the end time

## Conclusion
* `x t` is `x 0` plus the integral of `g` from zero to `t`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory intervalIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A derivative within a convex `T ∋ 0`, integrated from `0`, recovers the function. -/
theorem eq_add_integral_of_hasDerivWithinAt {T : Set ℝ} {x g : ℝ → E} (hTconv : Convex ℝ T)
    (h0T : (0:ℝ) ∈ T) (hd : ∀ t ∈ T, HasDerivWithinAt x (g t) T t) {t : ℝ} (ht : t ∈ T)
    (hint : IntervalIntegrable g volume 0 t) : -- --- CONCL ---
    x t = x 0 + ∫ s in (0:ℝ)..t, g s := by -- --- PROOF ---
  have hUIcc : Set.uIcc 0 t ⊆ T := hTconv.ordConnected.uIcc_subset h0T ht
  have hcont : ContinuousOn x (Set.uIcc 0 t) :=
    fun s hs => (hd s (hUIcc hs)).continuousWithinAt.mono hUIcc
  -- inside the window every point but its right end has room to its right in `T`
  have hderiv : ∀ s ∈ Set.Ioo (min (0:ℝ) t) (max (0:ℝ) t),
      HasDerivWithinAt x (g s) (Set.Ioi s) s := by
    intro s hs
    refine ((hd s (hUIcc ⟨hs.1.le, hs.2.le⟩)).mono_of_mem_nhdsWithin ?_).mono
      Set.Ioi_subset_Ici_self
    exact mem_nhdsGE_iff_exists_Ico_subset.mpr
      ⟨max 0 t, hs.2, fun _ hy => hUIcc ⟨hs.1.le.trans hy.1, hy.2.le⟩⟩
  rw [integral_eq_sub_of_hasDeriv_right hcont hderiv hint]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

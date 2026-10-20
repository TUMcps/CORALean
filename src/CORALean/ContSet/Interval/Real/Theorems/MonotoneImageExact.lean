module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Normed.Order.Lattice

@[expose] public section

/-!
# The image of a box under a monotone function

A strictly monotone function that is continuous on an interval `D` of the reals maps a box with
corners in `D` onto exactly the box of its endpoint images, by the intermediate value theorem
coordinate by coordinate. An antitone one swaps the two corners. Without continuity (`sign`,
`round`) only the outer statement holds: the image sits inside the box of endpoint images, with
no hypothesis on `f` beyond `Monotone`.

## Inputs
* `f` – function applied coordinatewise
* `D` – domain of `f`
* `I` – interval box

## Hypotheses
* `hD` – domain an interval
* `hf` – `f` strictly increasing on the domain
* `hc` – `f` continuous on the domain
* `hI` – bounds lie in the domain

## Conclusion
* the box of images of the bounds is exactly the image of `I`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Strictly increasing `f`, continuous on the interval `D`, corners in `D`. -/
theorem Interval.monotoneImage_exact (f : ℝ → ℝ) (D : Set ℝ) (hD : D.OrdConnected)
    (hf : StrictMonoOn f D) (hc : ContinuousOn f D) (I : Interval (Vec ℝ n))
    (hI : ∀ i, I.inf i ∈ D ∧ I.sup i ∈ D) : -- --- CONCL ---
    (⟨fun i => f (I.inf i), fun i => f (I.sup i)⟩ : Interval (Vec ℝ n)).construct
      = (fun x i => f (x i)) '' I.construct := by -- --- PROOF ---
  ext y
  constructor
  · intro hy
    have hy' : ∀ i, f (I.inf i) ≤ y i ∧ y i ≤ f (I.sup i) := fun i => hy i
    have hle : ∀ i, I.inf i ≤ I.sup i := fun i =>
      (hf.le_iff_le (hI i).1 (hI i).2).1 (le_trans (hy' i).1 (hy' i).2)
    have hex : ∀ i, ∃ x, x ∈ Set.Icc (I.inf i) (I.sup i) ∧ f x = y i := fun i =>
      intermediate_value_Icc (hle i) (hc.mono (hD.out (hI i).1 (hI i).2)) (hy' i)
    choose x hx hfx using hex
    exact ⟨x, fun i => hx i, funext hfx⟩
  · rintro ⟨x, hx, rfl⟩ i
    have hx' : I.inf i ≤ x i ∧ x i ≤ I.sup i := hx i
    have hxD : x i ∈ D := hD.out (hI i).1 (hI i).2 hx'
    exact ⟨hf.monotoneOn (hI i).1 hxD hx'.1, hf.monotoneOn hxD (hI i).2 hx'.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

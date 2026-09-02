import CORALean.ContSet.Interval.Real.Interval
import CORALean.Global.LinProg.API

/-!
# `Interval.ofBounds`

A box read off `2n` certified bounds, one per coordinate direction. Lower bounds
arrive as bounds against `-eⱼ`, a linear program bounding only from above.

This is what every representation's `interval` is once its bounds are in hand,
so the enclosure is proved once here rather than per representation.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ} {S : Set (Vec ℝ n)}

def Interval.ofBounds (up : ∀ j, SupportBound S (LinearMap.proj j))
    (lo : ∀ j, SupportBound S (-LinearMap.proj j)) : Interval (Vec ℝ n) where
  inf := fun j => -(lo j).val
  sup := fun j => (up j).val

theorem Interval.subset_ofBounds (up : ∀ j, SupportBound S (LinearMap.proj j))
    (lo : ∀ j, SupportBound S (-LinearMap.proj j)) :
    S ⊆ (Interval.ofBounds up lo).construct := by
  intro x hx j
  constructor
  · have h : -(x j) ≤ (lo j).val := (lo j).le x hx
    show -(lo j).val ≤ x j
    linarith
  · exact (up j).le x hx

end CORALean.Real

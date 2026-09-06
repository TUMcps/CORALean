import CORALean.ContSet.Interval.Real.Operations.OfBounds

/-!
# `Interval.ofBounds` encloses

The certified bounds are what says the box encloses the set they were computed
for.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {S : Set (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

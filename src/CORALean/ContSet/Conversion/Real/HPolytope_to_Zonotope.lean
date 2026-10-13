import CORALean.ContSet.Conversion.Real.HPolytope_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

/-!
# A halfspace description as a zonotope

Through its box, which is what the `2n` certificates give, and then the box's own
generators. Loses whatever the box lost and nothing further — a zonotope tight
around a halfspace description would have to know its facets.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}

noncomputable def HPolytope.zonotope (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : Zonotope (Vec ℝ n) :=
  (HPolytope.interval up lo).zonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.zonotope_contains (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.zonotope up lo).construct :=
  subset_trans (HPolytope.interval_contains up lo) (Interval.zonotope_contains _)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

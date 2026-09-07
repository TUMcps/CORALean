import CORALean.ContSet.Conversion.Real.HPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid

/-!
# A halfspace description as an ellipsoid

Through the zonotope the box gives. A direct minimum-volume enclosing
ellipsoid is a separate piece of mathematics; CORA computes one for a
halfspace description and this composition is not it.

Loses whatever the zonotope route loses on top of the box's own `2n` linear
programs.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}

noncomputable def HPolytope.ellipsoid (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : Ellipsoid n :=
  (HPolytope.zonotope up lo).ellipsoid


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ellipsoid_contains (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.ellipsoid up lo).construct :=
  subset_trans (HPolytope.zonotope_contains up lo) (Zonotope.ellipsoid_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

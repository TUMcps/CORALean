import CORALean.ContSet.Conversion.Real.HPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

/-!
# A halfspace description as a polynomial zonotope

Through the zonotope the box gives, then that zonotope's own exact reading as a
polynomial zonotope with one factor per generator. A direct polynomial
zonotope from halfspaces is a separate piece of mathematics, and its dependent
structure would go unused here regardless.

Loses whatever the box route loses and nothing further.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}

noncomputable def HPolytope.polyZonotope (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : PolyZonotope (Vec ℝ n) :=
  (HPolytope.zonotope up lo).polyZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.subset_polyZonotope (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.polyZonotope up lo).construct :=
  subset_trans (HPolytope.subset_zonotope up lo) (Zonotope.polyZonotope_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

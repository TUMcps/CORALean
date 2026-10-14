module

public import CORALean.ContSet.Conversion.Real.HPolytope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ConPolyZono

@[expose] public section

/-!
# A halfspace description as a constrained polynomial zonotope

Through the zonotope the box gives, then that zonotope's own exact reading as a
polynomial zonotope, then `PolyZonotope.conPolyZono` — an empty constraint
system, so that last leg adds nothing and is exact. All the loss is the box
route's, exactly as in `HPolytope.polyZonotope_contains`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.conPolyZono_contains (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.conPolyZono up lo).construct :=
  subset_trans (HPolytope.polyZonotope_contains up lo) (PolyZonotope.conPolyZono_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Conversion.Real.HPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

/-!
# A halfspace description as a bundle of one

Through the zonotope the box gives, then `Zonotope.zonoBundle` — the
single-member bundle, exact by `Set.iInter_const`. All the loss is the box
route's, so this is no worse than `HPolytope → Zonotope` already is.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}

noncomputable def HPolytope.zonoBundle (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : ZonoBundle (Vec ℝ n) :=
  (HPolytope.zonotope up lo).zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.subset_zonoBundle (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.zonoBundle up lo).construct :=
  subset_trans (HPolytope.subset_zonotope up lo) (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

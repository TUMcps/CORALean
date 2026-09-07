import CORALean.ContSet.ConPolyZono.Real.Operations.Domain
import CORALean.ContSet.ConPolyZono.Real.Operations.Affine

/-!
# A constrained polynomial zonotope is its domain's image

`construct` unbundled into the map and the coefficients it is applied to, which
is the reading compactness needs: the domain is a subset of a finite-dimensional
cube and the map is continuous, and neither statement can be made about the set
itself.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.construct_eq_image (cPZ : ConPolyZono α) :
    cPZ.construct = cPZ.affine '' cPZ.domain := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨(a, β), ⟨ha, hβ, hsat⟩, rfl⟩
  -- back, the two cubes and the constraint read off the domain again
  · rintro ⟨⟨a, β⟩, ⟨ha, hβ, hsat⟩, rfl⟩
    exact ⟨a, β, ha, hβ, hsat, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

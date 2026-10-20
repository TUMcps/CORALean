module

public import CORALean.ContSet.Zonotope.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.RepresentsaPoint

@[expose] public section

/-!
# `representsa` of a matrix zonotope is that of its vectorisation

CORA's `matZonotope/representsa` hands `zonotope(matZ)` to the vector class, so whatever it answers
is the answer. The two tests the library models for zonotopes (`representsa_point`,
`representsa_origin`) are the same on the stacked generators as on the matrices: the vectorisation
is injective. The set itself is preserved by `vec_construct`; the other types of CORA's
`representsa` are not modelled here.

## Inputs
* `Z` – matrix zonotope

## Hypotheses
* none

## Conclusion
* stacking preserves being a point or the origin
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Stacking the entries does not change whether the zonotope is a point or the origin. -/
theorem Zonotope.vec_representsa (Z : Zonotope (Mat ℝ m n)) : -- --- CONCL ---
    (Z.vec.representsa_point ↔ Z.representsa_point) ∧
    (Z.vec.representsa_origin ↔ Z.representsa_origin) := by -- --- PROOF ---
  have hG : ∀ j, Z.vec.G j = 0 ↔ Z.G j = 0 := fun j =>
    map_eq_zero_iff matVecEquiv.toLinearMap matVecEquiv.injective
  have hP : Z.vec.representsa_point ↔ Z.representsa_point :=
    forall_congr' hG
  refine ⟨hP, ?_⟩
  exact and_congr (map_eq_zero_iff matVecEquiv.toLinearMap matVecEquiv.injective) hP

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

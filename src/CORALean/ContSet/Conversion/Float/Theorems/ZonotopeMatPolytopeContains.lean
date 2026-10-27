module

public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_MatPolytope
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeVPolytopeContains
public import CORALean.ContSet.VPolytope.Float.Theorems.UnvecExact
public import CORALean.ContSet.Zonotope.Float.Theorems.VecExact

@[expose] public section

/-!
# `Zonotope.matPolytope` contains the matrix zonotope

The corners of the stacked zonotope contain it (`Zonotope.vPolytope_contains`), and stacking and
unstacking are exact, so the matrix polytope of the corners contains every member of the matrix
zonotope.

## Inputs
* `Z` – matrix zonotope

## Hypotheses
* none

## Conclusion
* every member of the zonotope lies in the corners' polytope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matPolytope_contains (Z : Zonotope (Mat 𝕋 m n)) : -- --- CONCL ---
    Z.construct ⊆ InflatedContSet.construct Z.matPolytope := by -- --- PROOF ---
  intro A hA
  -- the stacked matrix is in the stacked zonotope, hence in its corners
  have h1 : matVecEquiv A ∈ Z.vec.vPolytope.construct :=
    Zonotope.vPolytope_contains Z.vec (by rw [Zonotope.vec_exact]; exact ⟨A, hA, rfl⟩)
  rw [Zonotope.matPolytope, VPolytope.unvec_exact]
  exact ⟨_, h1, matVecEquiv.symm_apply_apply A⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.SupportFunction.Real.Operations.OfSet

@[expose] public section

/-!
# A polytope by vertices as a support function

The support function of the set it denotes, `sup {ℓ x | x ∈ P}`: the value of a linear program in
the one case and a maximum over the vertices in the other, computed by neither here. A polytope is
closed and convex, so its support function denotes it (`SupportFunction.ofSet_exact`).

## Inputs
* `P` – vertex polytope

## Output
* support function of the polytope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def VPolytope.supportFunction (P : VPolytope α) : SupportFunction α :=
  SupportFunction.ofSet P.construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

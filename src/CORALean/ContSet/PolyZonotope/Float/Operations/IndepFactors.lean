module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `PolyZonotope.indepFactors`

The map CORA's `@polyZonotope/contains_` tests containment against, `aux_funcPoly(x) =
c + Σ G(:,i)·prod(x₁.^E(:,i)) + GI·x₂`, as a polynomial zonotope without independent
generators: the independent generators become dependent ones, each with a factor of its own to
the first power, after the dependent factors. Nothing is rounded and the error box is kept, so
the dependent point map of the result at `(α, β)` is the nominal set's point at `(α, β)`. Unlike
`absorbRounding`, the error box is not turned into generators, which would enlarge the set.

## Inputs
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope with independent generators turned into factors
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The independent generators as dependent ones with factors of their own. -/
def PolyZonotope.indepFactors (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  ⟨pZ.p + pZ.q, pZ.h + pZ.q, 0, pZ.c, Fin.append pZ.G pZ.GI,
    Real.PolyZonotope.plusE pZ.E (Real.PolyZonotope.identE pZ.q), Fin.elim0, pZ.I_error⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

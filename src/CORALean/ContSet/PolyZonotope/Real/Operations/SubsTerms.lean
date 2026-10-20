module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsXprod

@[expose] public section

/-!
# `PolyZonotope.subsTerms`

One term per generator of the result: the generator `i` of `pZ` and a term of its `Xprod`.

## Inputs
* `pZ` – polynomial zonotope
* `nu` – number of substituted factors
* `pZin` – polynomial zonotope substituted in
* `idu` – indices of the substituted factors

## Output
* list of terms tagged with their generator
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators of the result, as pairs of an original generator and a term. -/
noncomputable def PolyZonotope.subsTerms (pZ : PolyZonotope α) {nu : ℕ}
    (pZin : PolyZonotope (Vec ℝ nu)) (idu : Fin nu → Fin pZ.p) :
    List (Fin pZ.h × (ℝ × (Fin pZin.p → ℕ))) :=
  (List.finRange pZ.h).flatMap fun i => (pZ.subsXprod pZin idu i).map fun t => (i, t)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# `ConZonotope.compactGens`

The generators `compact_ 'zeros'` keeps: those whose column of `[G; A]` has a nonzero entry,
that is, a generator that is nonzero or that some constraint reads. A constraint here is a
row of `P`, equality or inequality, read at the coefficient's unit vector, which the constraint's
own `HPolytope.colWeight` measures (zero exactly when no row reads it,
`HPolytope.colWeight_eq_zero_iff`).

## Inputs
* `cZ` – constrained zonotope

## Output
* indices of the generators kept
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators that are nonzero or constrained. -/
noncomputable def ConZonotope.compactGens (cZ : ConZonotope α) : Finset (Fin cZ.h) :=
  open Classical in
  Finset.univ.filter fun j =>
    cZ.G j ≠ 0 ∨ cZ.P.colWeight (Pi.single j (1 : ℝ) : Vec ℝ cZ.h) ≠ 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

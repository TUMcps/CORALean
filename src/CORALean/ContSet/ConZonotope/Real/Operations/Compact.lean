module

public import CORALean.ContSet.ConZonotope.Real.Operations.CompactGens
public import CORALean.ContSet.ConZonotope.Real.Operations.CompactEmbed
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.Comap

@[expose] public section

/-!
# `ConZonotope.compact`

CORA's `@conZonotope/compact_` with method `'zeros'`, which is also what `'all'` does: delete
the constraint rows that are `0 = 0`, then the generators whose column of `[G; A]` is zero.
Both are exact (`compact_exact`): a zero row constrains nothing, and a generator that is zero
and unconstrained adds nothing to the point whatever its coefficient. The tolerance is `0`;
CORA's `eps` removes columns of size below it as well.

Inequality rows stay, since CORA's constraint is an equality, and the kept generators keep their
order. Both steps are the constraint's own operations (#174): the rows `0 = 0` go by
`HPolytope.dropTrivialEqs`, and the rows are read on the kept generators by `HPolytope.comap`
along `compactEmbed`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `cZ` without its zero equality rows and its zero, unconstrained generators. -/
noncomputable def ConZonotope.compact (cZ : ConZonotope α) : ConZonotope α where
  h := cZ.compactGens.card
  c := cZ.c
  G := fun l => cZ.G (cZ.compactGens.orderIsoOfFin rfl l).1
  -- the rows without `0 = 0`, read on the kept coefficients
  P := (cZ.P.dropTrivialEqs).comap (ConZonotope.compactEmbed cZ.compactGens)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

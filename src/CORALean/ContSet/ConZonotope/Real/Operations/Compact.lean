import CORALean.ContSet.ConZonotope.Real.Operations.CompactGens
import CORALean.ContSet.ConZonotope.Real.Operations.CompactEqs
import CORALean.ContSet.ConZonotope.Real.Operations.CompactEmbed

/-!
# `ConZonotope.compact`

CORA's `@conZonotope/compact_` with method `'zeros'`, which is also what `'all'` does: delete
the constraint rows that are `0 = 0`, then the generators whose column of `[G; A]` is zero.
Both are exact (`compact_exact`): a zero row constrains nothing, and a generator that is zero
and unconstrained adds nothing to the point whatever its coefficient. The tolerance is `0`;
CORA's `eps` removes columns of size below it as well.

Inequality rows stay, since CORA's constraint is an equality, and the kept generators and
equality rows keep their order.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `cZ` without its zero equality rows and its zero, unconstrained generators. -/
noncomputable def ConZonotope.compact (cZ : ConZonotope α) : ConZonotope α where
  h := cZ.compactGens.card
  c := cZ.c
  G := fun l => cZ.G (cZ.compactGens.orderIsoOfFin rfl l).1
  P :=
    { m := cZ.P.m
      A := fun i => (cZ.P.A i).comp (ConZonotope.compactEmbed cZ.compactGens)
      b := cZ.P.b
      me := (ConZonotope.compactEqs cZ.P).card
      Ae := fun r => (cZ.P.Ae ((ConZonotope.compactEqs cZ.P).orderIsoOfFin rfl r).1).comp
        (ConZonotope.compactEmbed cZ.compactGens)
      be := fun r => cZ.P.be ((ConZonotope.compactEqs cZ.P).orderIsoOfFin rfl r).1 }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

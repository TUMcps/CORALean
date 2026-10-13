module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound

@[expose] public section

/-!
# Facet lifting: `HPolytope.facetLift`

[1, Prop. 3]: push every facet of `{x | Ex ≤ d}` outwards by what the added
zonotope reaches in that facet's direction, `d̃ᵢ = dᵢ + max(eᵢ Z_add)`. The reach is
`Zonotope.supportBound`, a sum of absolute values and no linear program.

The paper's `Z = {x | Ex ≤ d}` has inequality rows only, so the lift has none else:
equality rows of `P` are dropped, which only enlarges the set and keeps the
inclusion below.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.facetLift (P : HPolytope α) (Zadd : Zonotope α) : HPolytope α where
  m := P.m
  A := P.A
  b := fun i => P.b i + (Zadd.supportBound (P.A i)).val
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

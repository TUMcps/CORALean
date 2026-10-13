import CORALean.ContSet.Zonotope.Float.Operations.ContainsZonotope
import CORALean.ContSet.Zonotope.Float.Operations.RightInvCandidate

/-!
# `Zonotope.filterOut`, over a floating-point scalar

CORA's `@zonotope/filterOut(Z)` [1]: from a list of parallelotopes, delete those "covered by other
parallelotopes". CORA keeps a cell when it has a remainder after the set differences with all the
others (`chebyball` of the differences). A rounded layer cannot decide whether a union of
polytopes covers a cell, but it can certify the easiest cover: the cell lies in *one* other cell,
which `Zonotope.containsZonotope` checks (`'approx:st'` containment, with `rightInvCandidate` as
the proposed right inverse). A cell is kept unless some other cell is certified to contain it.

So the cells kept here are a superset of the cells whose remainder has nonempty interior
(`Zonotope.filterOut_keeps`): nothing the criterion keeps is deleted, but a cell covered only by
a union of several cells is kept, which the criterion deletes. As in CORA, two equal cells delete
each other. The sort by volume only orders CORA's output list and is not modelled.

## References

* [1] `contSet/@zonotope/filterOut.m`, CORA (Sep. 2025), by M. Althoff (2008). No paper behind the
      rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The cells that survive: those no other cell is certified to contain. -/
def Zonotope.filterOut (Zs : Fin m → Zonotope (Vec 𝕋 n)) : Finset (Fin m) :=
  let covered := fun (ind j : Fin m) =>                              -- P_ind \ P_j has no remainder
    (Zs j).containsZonotope (Zs ind) (Zonotope.rightInvCandidate fun i k => (Zs j).G k i)
  Finset.univ.filter fun ind => (List.finRange m).all fun j => j = ind || !covered ind j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

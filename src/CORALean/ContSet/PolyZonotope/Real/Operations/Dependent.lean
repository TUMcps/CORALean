import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

/-!
# `PolyZonotope.dependent`

Every independent generator made dependent, by giving it a fresh factor that
appears in it alone and to the first power. Exact, and cheaply so: a factor
occurring in one generator only is as free as the coefficient it replaces.

CORA has no method for this — its `restructure` goes the other way, buying a
smaller exponent matrix by making dependent generators independent. This
direction exists here because `quadMap` is stated on a set whose coefficients
are all dependent, and it is what lets `quadMap` be total without pretending
about the cross terms an independent block would contribute.

The exponent matrix is `plusE` against the identity, which is exactly right: the
fresh factors must not reach the original generators, and the original factors
must not reach the freed ones.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def PolyZonotope.dependent (PZ : PolyZonotope α) : PolyZonotope α where
  p := PZ.p + PZ.q
  h := PZ.h + PZ.q
  q := 0
  c := PZ.c
  G := Fin.append PZ.G PZ.GI
  E := PolyZonotope.plusE PZ.E (PolyZonotope.identE PZ.q)
  GI := Fin.elim0

end CORALean.Real

import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.ConPolyZono.Real.Operations.Compact
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.Compact

/-!
# `ConPolyZono.compact`

The exact layer's three stages, with the obstacles traded as they are for
`PolyZonotope`: no zero test is made, costing a column that denotes nothing
rather than soundness, and which columns survive is decided structurally by
`repKeep`, one per class. What appears instead is arithmetic, merging two
columns being an addition.

The two merges pay into different places, which is the whole of what the
constraints add. A merged *generator* column is off by the gap between the two
directed masked sums, and that gap is a `generatorError` in the ambient box, as
for `PolyZonotope`. A merged *constraint* column has no ambient box to pay into
— its rows live in `Fin m`, not in the state — so it pays into `b`: the row is
off by at most `radius` of the row of gaps, the monomials being in `[-1,1]`, and
`b` is widened by that, downward on the low side and upward on the high.

`compactFactors` changes `p` and both exponent matrices and nothing else, all
over ℕ, so its nominal part is literally the exact layer's.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-! ## The generators -/

/-- The merged generator column as stored: the lower of the two directed fibre
sums, `repKeep` naming the one column per class that survives. -/
def ConPolyZono.mergedCol (C : ConPolyZono 𝕋 n) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep C.E).card) : 𝕋 :=
  PolyZonotope.fiberDown (Real.PolyZonotope.rep C.E) C.G i (PolyZonotope.keepIdx C.E j)

/-- The same fibre rounded the other way, which is what bounds the gap. -/
def ConPolyZono.mergedColUp (C : ConPolyZono 𝕋 n) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep C.E).card) : 𝕋 :=
  PolyZonotope.fiberUp (Real.PolyZonotope.rep C.E) C.G i (PolyZonotope.keepIdx C.E j)

/-- What a merged generator column can be off by. -/
def ConPolyZono.compactGensGap (C : ConPolyZono 𝕋 n) :
    Mat 𝕋 n (PolyZonotope.repKeep C.E).card :=
  fun i j => subUp (C.mergedColUp i j) (C.mergedCol i j)

/-- Equal exponent columns added together, the stored value the lower rounding
and the gap paid into the ambient box. The constraint block stands. -/
def ConPolyZono.compactGens (C : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := C.p
  h := (PolyZonotope.repKeep C.E).card
  q := C.q
  m := C.m
  s := C.s
  c := C.c
  G := C.mergedCol
  E := fun k j => C.E k (PolyZonotope.keepIdx C.E j)
  GI := C.GI
  A := C.A
  b := C.b
  EC := C.EC
  err := C.err.plus (PolyZonotope.generatorError (ConPolyZono.compactGensGap C))

/-! ## The constraints -/

/-- The merged constraint column as stored, `A`'s rows read as the generator
matrix they are on the constraint side. -/
def ConPolyZono.mergedConsCol (C : ConPolyZono 𝕋 n) (i : Fin C.m)
    (l : Fin (PolyZonotope.repKeep C.EC).card) : 𝕋 :=
  PolyZonotope.fiberDown (Real.PolyZonotope.rep C.EC) C.A i (PolyZonotope.keepIdx C.EC l)

def ConPolyZono.mergedConsColUp (C : ConPolyZono 𝕋 n) (i : Fin C.m)
    (l : Fin (PolyZonotope.repKeep C.EC).card) : 𝕋 :=
  PolyZonotope.fiberUp (Real.PolyZonotope.rep C.EC) C.A i (PolyZonotope.keepIdx C.EC l)

/-- What a merged constraint column can be off by. -/
def ConPolyZono.compactConsGap (C : ConPolyZono 𝕋 n) :
    Mat 𝕋 C.m (PolyZonotope.repKeep C.EC).card :=
  fun i l => subUp (C.mergedConsColUp i l) (C.mergedConsCol i l)

/-- `b` widened by what a merged row can be off by. Every constraint monomial is
in `[-1,1]`, so a row's whole error is one `radius` of its gaps, and rounding it
outward on both sides is what keeps the constraint admitting what it did. -/
def ConPolyZono.compactConsB (C : ConPolyZono 𝕋 n) : Interval 𝕋 C.m :=
  ⟨fun i => subDown (C.b.inf i) (radius (ConPolyZono.compactConsGap C) i),
    fun i => addUp (C.b.sup i) (radius (ConPolyZono.compactConsGap C) i)⟩

/-- Equal constraint exponent columns added together, the stored value the lower
rounding and the widening paid into `b`. The generators stand, so the ambient
box is untouched. -/
def ConPolyZono.compactCons (C : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := C.p
  h := C.h
  q := C.q
  m := C.m
  s := (PolyZonotope.repKeep C.EC).card
  c := C.c
  G := C.G
  E := C.E
  GI := C.GI
  A := C.mergedConsCol
  b := ConPolyZono.compactConsB C
  EC := fun k l => C.EC k (PolyZonotope.keepIdx C.EC l)
  err := C.err

/-! ## The factors -/

/-- The factors neither block reads, dropped. Only `p` and the two exponent
matrices change, all over ℕ, so nothing rounds and neither `b` nor the box
moves. -/
def ConPolyZono.compactFactors (C : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := (Real.ConPolyZono.usedFactors C.E C.EC).card
  h := C.h
  q := C.q
  m := C.m
  s := C.s
  c := C.c
  G := C.G
  E := fun k i => C.E (Real.ConPolyZono.factorIdx C.E C.EC k) i
  GI := C.GI
  A := C.A
  b := C.b
  EC := fun k l => C.EC (Real.ConPolyZono.factorIdx C.E C.EC k) l
  err := C.err

/-- CORA's `compact`: the generators, then the constraints, then the factors
that fell out of use. -/
def ConPolyZono.compact (C : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n :=
  C.compactGens.compactCons.compactFactors

end CORALean.Float

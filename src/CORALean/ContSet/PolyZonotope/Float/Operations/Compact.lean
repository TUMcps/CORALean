import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

/-!
# `PolyZonotope.compact`

The exact layer's `compact`, with the obstacles traded. The zero test on a
merged generator is simply not made here, costing a column that denotes nothing
rather than soundness; what appears instead is arithmetic, since merging two
columns adds their entries and a directed sum owes an error box.

Which columns survive is decided structurally: one per class, the least index
carrying that exponent column, which is `Real.PolyZonotope.rep`. `repKeep` is
its fixed points, and `card` of it is the monomial count `reduce` wanted.

A fibre is a *masked* sum over all of `Fin h`: a column outside the fibre
contributes `zero`, and `addUp a zero` is sound, so `sumDown` and `sumUp`
bracket the exact fibre sum. Both directions are computed, the lower stored and
the gap charged as a `generatorError`, the coefficient being a monomial.

`compactFactors` changes `p` and the exponent matrix and nothing else, all over
ℕ, so its nominal part is literally the exact layer's.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n p h : ℕ}

/-- The columns that survive: one per exponent column, the least index carrying
it. A column that is not its class's representative has an empty fibre, so
merging and dropping are one step here as they are over ℝ. -/
def PolyZonotope.repKeep (E : Fin p → Fin h → ℕ) : Finset (Fin h) :=
  Finset.univ.filter fun j => Real.PolyZonotope.rep E j = j

/-- The kept columns indexed by a plain count, which is what the field `h` needs
and a `Finset` is not. -/
def PolyZonotope.keepIdx (E : Fin p → Fin h → ℕ)
    (j : Fin (PolyZonotope.repKeep E).card) : Fin h :=
  (PolyZonotope.repKeep E).orderIsoOfFin rfl j

/-- A fibre summed downward, masked rather than restricted: the columns outside
it contribute `zero`, which is what lets `sumDown` over `Fin h` answer a sum
over a `Finset`. -/
def PolyZonotope.fiberDown (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n) (j : Fin h) : 𝕋 :=
  sumDown fun l => if r l = j then G i l else zero

def PolyZonotope.fiberUp (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n) (j : Fin h) : 𝕋 :=
  sumUp fun l => if r l = j then G i l else zero

/-- The merged column as stored: the lower of the two directed fibre sums. -/
def PolyZonotope.mergedCol (PZ : PolyZonotope 𝕋 n) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep PZ.E).card) : 𝕋 :=
  PolyZonotope.fiberDown (Real.PolyZonotope.rep PZ.E) PZ.G i (PolyZonotope.keepIdx PZ.E j)

/-- The same fibre rounded the other way, which is what bounds the gap. -/
def PolyZonotope.mergedColUp (PZ : PolyZonotope 𝕋 n) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep PZ.E).card) : 𝕋 :=
  PolyZonotope.fiberUp (Real.PolyZonotope.rep PZ.E) PZ.G i (PolyZonotope.keepIdx PZ.E j)

/-- What a merged column can be off by. -/
def PolyZonotope.compactGap (PZ : PolyZonotope 𝕋 n) :
    Mat 𝕋 n (PolyZonotope.repKeep PZ.E).card :=
  fun i j => subUp (PZ.mergedColUp i j) (PZ.mergedCol i j)

/-- Equal exponent columns added together, the stored value the lower rounding
and the gap paid into the box. The factors are untouched. -/
def PolyZonotope.compactGens (PZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 n where
  p := PZ.p
  h := (PolyZonotope.repKeep PZ.E).card
  q := PZ.q
  c := PZ.c
  G := PZ.mergedCol
  E := fun k j => PZ.E k (PolyZonotope.keepIdx PZ.E j)
  GI := PZ.GI
  err := PZ.err.plus (PolyZonotope.generatorError (PolyZonotope.compactGap PZ))

/-- The factors no column reads, dropped. Only `p` and the exponent matrix
change, both over ℕ, so nothing rounds and the box is untouched. -/
def PolyZonotope.compactFactors (PZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 n where
  p := (Real.PolyZonotope.usedFactors PZ.E).card
  h := PZ.h
  q := PZ.q
  c := PZ.c
  G := PZ.G
  E := fun k i => PZ.E (Real.PolyZonotope.factorIdx PZ.E k) i
  GI := PZ.GI
  err := PZ.err

/-- CORA's `compact`: merge, then drop the factors that fell out of use. -/
def PolyZonotope.compact (PZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 n :=
  PZ.compactGens.compactFactors

end CORALean.Float

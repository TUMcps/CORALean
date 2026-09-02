import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

/-!
# `PolyZonotope.compact`

The exact layer's `compact`, and the two obstacles trade places exactly as
`Reduce` predicted. What blocks the exact one — deciding whether a merged
generator is zero in an arbitrary real module — is *not* what blocks this one:
that test is simply not made here, and it costs a column that denotes nothing
rather than soundness. What appears instead is arithmetic. Merging two columns
adds their entries, and a directed sum is not a sum, so a float `compact` owes
an error box where the exact one is an equality.

Which columns survive is therefore decided structurally: one per class, the
least index carrying that exponent column, which is `Real.PolyZonotope.rep`
already. `repKeep` is its fixed points, and `card` of it is the number of
distinct monomials — which is what `reduce` wanted to bound and could not.

The `Finset` sum is the other half of what `Reduce` said was missing, and it
does not need a new `sumUp`. A fibre is a *masked* sum over all of `Fin h`:
every column outside the fibre contributes `zero`, and `addUp a zero` is still
sound, so `sumDown` and `sumUp` over `Fin h` bracket the exact fibre sum with
the summation order the layer already fixes. The masking costs precision on the
`zero`s and nothing else.

Both directions are computed, the lower stored and the gap charged. Charged as a
`generatorError` rather than as a `residual`, the merged column's coefficient
being a monomial that reaches `[-1,1]`.

`compactFactors` needs none of this. It changes `p` and the exponent matrix and
nothing else, all of it over ℕ, so the nominal part of the result is literally
the exact layer's `compactFactors` of the nominal part.

Computable, where the exact `compact` is not: an exponent column is a
`Fin p → ℕ` and equality on it is decidable, which was the only classical step
once the zero test is gone.
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

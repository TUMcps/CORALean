import CORALean.ContSet.Interval.Float.Operations.LinComb
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Interval.Float.Operations.Symmetric
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb

/-!
# `PolyZonotope.linComb`

The exact layer's three dependent blocks, and only two vectors round in all of
them. Halving is exact and so is negation, so `½G₁`, `½G₂` and `-½G₂` are
copies, and the exponent matrix is `linCombE` over ℕ — reused rather than
restated, nothing about it rounding. The independent block concatenates.

What is left is what a zonotope's `linComb` already pays: the midpoint that
becomes the new centre, and the half-difference that becomes the sliding
generator. They are charged differently — the midpoint is stored in place of a
known bracket, which is a `residual`, while the sliding generator's coefficient
is the fresh factor and ranges over `[-1,1]`, so its shortfall pulls both ways
and needs a symmetric box.

So the float `linComb` costs exactly one centre rounding more than the exact
one, independently of `p`, of the degree and of both generator counts. That is
the same statement `MemGeneratorError` makes about `plus` and `mtimes`, and here
it is sharper still: the dependent blocks are not merely cheap to round, they do
not round at all.

Not `Zonotope.midpoint` and friends, which are the same expressions: the two
representations stay independent of each other.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The stored midpoint of the two centres. -/
def PolyZonotope.midpoint (a b : Vec 𝕋 n) : Vec 𝕋 n := fun i => half (addDown (a i) (b i))

/-- The stored half-difference of the two centres: the generator the fresh
factor slides along. -/
def PolyZonotope.halfDiff (a b : Vec 𝕋 n) : Vec 𝕋 n := fun i => half (subDown (a i) (b i))

/-- Storing the lower of the two directed midpoints leaves this much to pay. -/
def PolyZonotope.midpointResidual (a b : Vec 𝕋 n) : Interval 𝕋 n :=
  Interval.residual (fun i => half (addDown (a i) (b i)))
    (fun i => half (addUp (a i) (b i))) (PolyZonotope.midpoint a b)

/-- What the sliding generator falls short by, over the whole range of the fresh
factor: the stored value rounds down, so the gap to the upper rounding bounds
it, and `[-1,1]` spreads that gap symmetrically. -/
def PolyZonotope.halfDiffError (a b : Vec 𝕋 n) : Interval 𝕋 n :=
  Interval.symmetric fun i =>
    subUp (half (subUp (a i) (b i))) (half (subDown (a i) (b i)))

def PolyZonotope.linComb (PZ₁ PZ₂ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 n where
  p := PZ₁.p + PZ₂.p + 1
  h := PZ₁.h + PZ₂.h + (PZ₁.h + PZ₂.h + 1)
  q := PZ₁.q + PZ₂.q
  c := PolyZonotope.midpoint PZ₁.c PZ₂.c
  G := fun i => Fin.append
        (Fin.append (fun l => half (PZ₁.G i l)) (fun l => half (PZ₂.G i l)))
        (Fin.append
          (Fin.append (fun l => half (PZ₁.G i l)) (fun l => neg (half (PZ₂.G i l))))
          (fun _ : Fin 1 => PolyZonotope.halfDiff PZ₁.c PZ₂.c i))
  E := Real.PolyZonotope.linCombE PZ₁.E PZ₂.E
  GI := fun i => Fin.append (PZ₁.GI i) (PZ₂.GI i)
  err := (PZ₁.err.linComb PZ₂.err).plus
    ((PolyZonotope.midpointResidual PZ₁.c PZ₂.c).plus
      (PolyZonotope.halfDiffError PZ₁.c PZ₂.c))

end CORALean.Float

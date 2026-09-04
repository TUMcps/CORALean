import CORALean.ContSet.Interval.Float.Operations.LinComb
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Interval.Float.Operations.Symmetric
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError
import CORALean.ContSet.Zonotope.Float.Operations.LinComb

/-!
# `PolyZonotope.linComb`

The exact layer's three dependent blocks, and nothing in any of them rounds.
Halving is exact and so is negation, so `½G₁`, `½G₂` and `-½G₂` are copies, and
`linCombE` is over ℕ.

Three vectors' worth of rounding is what is left, in two kinds. The centre and
the sliding generator are what a zonotope's `linComb` already pays: a midpoint
stored in place of a known bracket is a `residual`, while the sliding
generator's coefficient ranges over `[-1,1]`, so its shortfall pulls both ways
and needs a symmetric box. The independent block pairs, and a pairing is
arithmetic, so `generatorError` charges its whole matrix at once. The dependent
side is therefore free, and both counts are what they are over ℝ.

`Zonotope.pairSum`, `Zonotope.pairDiff` and `Zonotope.generatorError` are
borrowed rather than restated, as CORA's `@polyZonotope/linComb` runs
`zonotope/enclose` on the independent blocks. The midpoint and the sliding
generator stay local, being one-line expressions that happen to coincide.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
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

/-- The independent block at one rounding: CORA's `zonotope/enclose` on the two
independent blocks, which is the exact layer's pairing at a zero centre. -/
def PolyZonotope.linCombGI (add sub : 𝕋 → 𝕋 → 𝕋) (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    Mat 𝕋 n (PZ₁.q + PZ₂.q) :=
  fun i => Fin.append (Zonotope.pairSum add (PZ₁.GI i) (PZ₂.GI i))
    (Zonotope.pairDiff sub (PZ₁.GI i) (PZ₂.GI i))

/-- What the stored independent generators fall short by: the gap between the
two directed roundings, which a coefficient in `[-1,1]` then spreads either
way. -/
def PolyZonotope.linCombGIDiff (PZ₁ PZ₂ : PolyZonotope 𝕋 n) : Mat 𝕋 n (PZ₁.q + PZ₂.q) :=
  fun i j => subUp (PolyZonotope.linCombGI addUp subUp PZ₁ PZ₂ i j)
    (PolyZonotope.linCombGI addDown subDown PZ₁ PZ₂ i j)

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
  GI := PolyZonotope.linCombGI addDown subDown PZ₁ PZ₂
  err := (PZ₁.err.linComb PZ₂.err).plus
    ((PolyZonotope.midpointResidual PZ₁.c PZ₂.c).plus
      ((PolyZonotope.halfDiffError PZ₁.c PZ₂.c).plus
        (Zonotope.generatorError (PolyZonotope.linCombGIDiff PZ₁ PZ₂))))

end CORALean.Float

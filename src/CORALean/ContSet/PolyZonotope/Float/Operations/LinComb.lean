import CORALean.ContSet.Interval.Float.Operations.LinComb
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiffError
import CORALean.ContSet.PolyZonotope.Float.Operations.LinCombGIDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.Midpoint
import CORALean.ContSet.PolyZonotope.Float.Operations.MidpointResidual
import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError

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
`zonotope/enclose` on the independent blocks. `midpoint` and `halfDiff` are
one-line expressions that happen to coincide.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

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

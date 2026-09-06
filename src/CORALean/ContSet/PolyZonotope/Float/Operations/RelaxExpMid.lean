import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxCentreMid
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGapMid
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenMid
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMid

/-!
# `PolyZonotope.relaxExpMid`

The exact layer's `relaxExpMid`, rounded. The bracket `eDrift` reads is a pair
of counts, so the midpoint and the half-width are halves of natural multiples of
one stored generator: `half` is exact and the two layers shift and pay the same
amount, as they already relax by the same width.

The shift is a difference of two folds, so it has no sign to case on. It is
stored at its lower rounding and added to the centre downward, which keeps the
stored centre below the exact one; its gap is then the distance up to the same
sum taken at the shift's *upper* rounding, one-sided like every other gap here.

Three sums round, as in the all-even case: the merged dependent column, the
halved independent one, and the shifted centre. `generatorError` charges each
gap at the coefficient that reads it — a monomial, a zonotope coefficient, and
`1` for the centre.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two generators `part.right` names merged into one, the drift's midpoint
moved into the centre and its half-width into a new independent generator. -/
def PolyZonotope.relaxExpMid (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : PolyZonotope 𝕋 n where
  p := PZ.p
  h := d + 1
  q := PZ.q + 1
  c := PZ.relaxCentreMid part k₀
  G := fun i => Fin.append (fun l => PZ.G i (part.left l)) (fun _ => PZ.mergedGen part i)
  E := fun k => Fin.append (fun l => PZ.E k (part.left l)) (fun _ => PZ.E k (part.right 1))
  GI := fun i => Fin.append (PZ.GI i) (fun _ => PZ.relaxGenMid part k₀ i)
  err := PZ.err.plus (PolyZonotope.generatorError (PZ.relaxGapMid part k₀))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

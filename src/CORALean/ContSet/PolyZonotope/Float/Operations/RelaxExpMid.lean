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
def PolyZonotope.relaxExpMid (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : PolyZonotope 𝕋 n where
  p := pZ.p
  h := d + 1
  q := pZ.q + 1
  c := pZ.relaxCentreMid part k₀
  G := Fin.append (fun l => pZ.G (part.left l)) (fun _ => pZ.mergedGen part)
  E := fun k => Fin.append (fun l => pZ.E k (part.left l)) (fun _ => pZ.E k (part.right 1))
  GI := Fin.append pZ.GI (fun _ => pZ.relaxGenMid part k₀)
  err := pZ.err.plus (PolyZonotope.generatorError (pZ.relaxGapMid part k₀))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

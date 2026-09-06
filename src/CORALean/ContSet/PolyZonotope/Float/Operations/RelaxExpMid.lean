import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExp
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

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}

/-- The drift's two reaches, read off the exponent matrix and so the exact
layer's own bracket. -/
def PolyZonotope.relaxDrift (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : ℕ × ℕ :=
  Real.PolyZonotope.eDrift PZ.E k₀ (part.right 0) (part.right 1)

/-- The centre shift as stored: half the upward reach less half the downward
one, in copies of the relaxed generator, rounded down. -/
def PolyZonotope.relaxShiftMid (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => half (subDown (nsmulDown (PZ.relaxDrift part k₀).2 (PZ.G i (part.right 0)))
    (nsmulUp (PZ.relaxDrift part k₀).1 (PZ.G i (part.right 0))))

/-- The same shift rounded up, which the centre's gap reads. -/
def PolyZonotope.relaxShiftMidUp (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => half (subUp (nsmulUp (PZ.relaxDrift part k₀).2 (PZ.G i (part.right 0)))
    (nsmulDown (PZ.relaxDrift part k₀).1 (PZ.G i (part.right 0))))

/-- The new independent column as stored: half of as many copies of the relaxed
generator as the bracket is wide, rounded down. -/
def PolyZonotope.relaxGenMid (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulDown ((PZ.relaxDrift part k₀).1 + (PZ.relaxDrift part k₀).2)
    (PZ.G i (part.right 0)))

/-- The same fold rounded up, which only that column's gap reads. -/
def PolyZonotope.relaxGenMidUp (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulUp ((PZ.relaxDrift part k₀).1 + (PZ.relaxDrift part k₀).2)
    (PZ.G i (part.right 0)))

/-- The shifted centre as stored, the shift added at its lower rounding, so the
stored centre stays below the exact one. -/
def PolyZonotope.relaxCentreMid (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => addDown (PZ.c i) (PZ.relaxShiftMid part k₀ i)

/-- What the merged column, the halved column and the shifted centre can each be
off by, every one of them a gap between two roundings of one expression. -/
def PolyZonotope.relaxGapMid (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Mat 𝕋 n 3 :=
  fun i =>
    ![subUp (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0))) (PZ.mergedGen part i),
      subUp (PZ.relaxGenMidUp part k₀ i) (PZ.relaxGenMid part k₀ i),
      subUp (addUp (PZ.c i) (PZ.relaxShiftMidUp part k₀ i)) (PZ.relaxCentreMid part k₀ i)]

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

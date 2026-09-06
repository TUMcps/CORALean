import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExp
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpEven

/-!
# `PolyZonotope.relaxExpEven`

The exact layer's `relaxExpEven`, rounded. `half` is exact, so the `ξ_E/2` the
recentring asks for costs nothing beyond what `ξ_E` copies of the generator
already cost: the width stays a count read off the exponent matrix, and both
layers relax by the same amount.

Three sums round here where `relaxExp` has two. The merged dependent column and
the halved independent one are stored downward; the recentred centre is a
subtraction, and it is stored downward too by taking the *upward* rounding of
the shift off it, so it stays below the exact centre and its gap is one-sided
like the others.

Each gap is the width between the two roundings of one expression, which is what
`generatorError` charges to the box — at coefficient `1` for the centre, at a
monomial or a zonotope coefficient for the two columns.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}

/-- Half of `ξ_E` copies of the relaxed generator, rounded down: the new
independent column, and the size of the centre shift. -/
def PolyZonotope.relaxGenEven (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulDown (PZ.relaxWidth part k₀) (PZ.G i (part.right 0)))

/-- The same fold rounded up, which only the centre and the gaps read. -/
def PolyZonotope.relaxGenEvenUp (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulUp (PZ.relaxWidth part k₀) (PZ.G i (part.right 0)))

/-- The recentred centre as stored: the shift taken off at its upper rounding,
so the stored centre stays below the exact one. -/
def PolyZonotope.relaxCentreEven (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => subDown (PZ.c i) (PZ.relaxGenEvenUp part k₀ i)

/-- What the merged column, the halved column and the recentred centre can each
be off by, every one of them a gap between two roundings of one expression. -/
def PolyZonotope.relaxGapEven (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Mat 𝕋 n 3 :=
  fun i =>
    ![subUp (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0))) (PZ.mergedGen part i),
      subUp (PZ.relaxGenEvenUp part k₀ i) (PZ.relaxGenEven part k₀ i),
      subUp (subUp (PZ.c i) (PZ.relaxGenEven part k₀ i)) (PZ.relaxCentreEven part k₀ i)]

/-- `relaxExp` with the drift's midpoint taken off the centre, so the new
independent generator carries only its radius. -/
def PolyZonotope.relaxExpEven (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : PolyZonotope 𝕋 n where
  p := PZ.p
  h := d + 1
  q := PZ.q + 1
  c := PZ.relaxCentreEven part k₀
  G := fun i => Fin.append (fun l => PZ.G i (part.left l)) (fun _ => PZ.mergedGen part i)
  E := fun k => Fin.append (fun l => PZ.E k (part.left l)) (fun _ => PZ.E k (part.right 1))
  GI := fun i => Fin.append (PZ.GI i) (fun _ => PZ.relaxGenEven part k₀ i)
  err := PZ.err.plus (PolyZonotope.generatorError (PZ.relaxGapEven part k₀))

end CORALean.Float

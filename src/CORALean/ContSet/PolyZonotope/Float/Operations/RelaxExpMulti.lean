import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExp
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti

/-!
# `PolyZonotope.relaxExpMulti`

The exact layer's `relaxExpMulti`, rounded. It rounds where `relaxExp` rounds
and nowhere else: the merged dependent column is the same sum of two stored
floats, so `mergedGen` is reused rather than restated, and the new independent
column is again a fold of copies of one generator — only how many copies has
changed.

The count itself rounds nothing. `eDiff` is over ℕ in both layers and the
exponent matrix is copied, so the summed width is a natural number the two
layers agree on exactly, however many factors it runs over. What that buys is
that a wider relaxation costs no extra box: the fold is one `nsmulDown` at the
larger count, not a chain of them.

The centre is untouched, `ξ_c` being zero at `ξ_G = ξ_E`, so this operation adds
the same two gaps to the box that `relaxExp` does.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}

/-- `ξ_E` summed over every factor, read off the exponent matrix and so the
exact layer's own width. -/
def PolyZonotope.relaxWidthMulti (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) : ℕ :=
  ∑ k, Real.PolyZonotope.eDiff (PZ.E k (part.right 0)) (PZ.E k (part.right 1))

/-- The new independent generator as stored: the summed `ξ_E` copies of the
relaxed generator, rounded down. -/
def PolyZonotope.relaxGenMulti (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) : Vec 𝕋 n :=
  fun i => nsmulDown (PZ.relaxWidthMulti part) (PZ.G i (part.right 0))

/-- What the two stored columns can be off by, each the gap to the other
rounding direction of the same sum. -/
def PolyZonotope.relaxGapMulti (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) : Mat 𝕋 n 2 :=
  fun i =>
    ![subUp (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0))) (PZ.mergedGen part i),
      subUp (nsmulUp (PZ.relaxWidthMulti part) (PZ.G i (part.right 0)))
        (PZ.relaxGenMulti part i)]

/-- The two generators `part.right` names merged into one, at the exponent
column of the second, the first scaled by the summed `ξ_E` becoming
independent. -/
def PolyZonotope.relaxExpMulti (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) : PolyZonotope 𝕋 n where
  p := PZ.p
  h := d + 1
  q := PZ.q + 1
  c := PZ.c
  G := fun i => Fin.append (fun l => PZ.G i (part.left l)) (fun _ => PZ.mergedGen part i)
  E := fun k => Fin.append (fun l => PZ.E k (part.left l)) (fun _ => PZ.E k (part.right 1))
  GI := fun i => Fin.append (PZ.GI i) (fun _ => PZ.relaxGenMulti part i)
  err := PZ.err.plus (PolyZonotope.generatorError (PZ.relaxGapMulti part))

end CORALean.Float

import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGapMulti
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenMulti
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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

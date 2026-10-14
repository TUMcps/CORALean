module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGapMulti
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenMulti
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti

@[expose] public section

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

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two generators `part.right` names merged into one, at the exponent
column of the second, the first scaled by the summed `ξ_E` becoming
independent. -/
def PolyZonotope.relaxExpMulti (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := d + 1
  q := pZ.q + 1
  c := pZ.c
  G := Fin.append (fun l => pZ.G (part.left l)) (fun _ => pZ.mergedGen part)
  E := fun k => Fin.append (fun l => pZ.E k (part.left l)) (fun _ => pZ.E k (part.right 1))
  GI := Fin.append pZ.GI (fun _ => pZ.relaxGenMulti part)
  I_error := pZ.I_error.plus (PolyZonotope.generatorError (pZ.relaxGapMulti part))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

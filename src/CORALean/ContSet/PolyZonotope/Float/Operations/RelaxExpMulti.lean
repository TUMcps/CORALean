module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxWidthMulti
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti

@[expose] public section

/-!
# `PolyZonotope.relaxExpMulti`

The exact layer's `relaxExpMulti`, rounded. It rounds where `relaxExp` rounds and nowhere else:
the merged dependent column is the same sum of two stored floats (`mergedGen` is reused) and
the new independent column is again a fold of copies of one generator, only the number of
copies has changed. The count rounds nothing: `eDiff` is over ℕ in both layers, so a wider
relaxation costs no extra box (one `nsmulDown` at the larger count). The center is untouched,
so the box gets the same two gaps as `relaxExp`.

## Inputs
* `pZ` – polynomial zonotope
* `part` – split with two selected generators

## Output
* polynomial zonotope relaxed over all factors
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}
open FloatOps


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The new independent generator as stored: the summed `ξ_E` copies of the
relaxed generator, rounded down. -/
def PolyZonotope.aux_relaxGenMulti (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) : Vec 𝕋 n :=
  fun i => nsmulDown (pZ.relaxWidthMulti part) (pZ.G (part.right 0) i)

/-- What the two stored columns can be off by, each the gap to the other
rounding direction of the same sum. -/
def PolyZonotope.aux_relaxGapMulti (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) : Mat 𝕋 n 2 :=
  fun i =>
    ![subUp (addUp (pZ.G (part.right 1) i) (pZ.G (part.right 0) i)) (pZ.mergedGen part i),
      subUp (nsmulUp (pZ.relaxWidthMulti part) (pZ.G (part.right 0) i))
        (pZ.aux_relaxGenMulti part i)]


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
  GI := Fin.append pZ.GI (fun _ => pZ.aux_relaxGenMulti part)
  I_error := pZ.I_error.plus (PolyZonotope.generatorError (pZ.aux_relaxGapMulti part))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

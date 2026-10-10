import CORALean.Global.BlockDiag
import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.SpectraShadow.Float.Operations.Absorb
import CORALean.ContSet.SpectraShadow.Float.Operations.ArrowMat

/-!
# `SpectraShadow.cone`, over a floating-point scalar

The conic hull `aux_conicHull` of `@spectraShadow/convHull_.m`, as the exact layer has it
(`Real.SpectraShadow.cone`): the shadow's own matrices scaled by the free variable `s`, the
generators and the centre as columns of the homogenised point, and the arrowhead block. The error
box is absorbed into the inequality first (`absorb`), as the cone of a box-inflated shadow is not
the cone of its nominal part. Every stored entry is a stored float, `zero` or `one`, so nothing
rounds and the box left over is the origin.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps CORALean

variable {𝕋 : Type} [FloatOps 𝕋] {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.cone (T : SpectraShadow 𝕋 N) : SpectraShadow 𝕋 N :=
  let T' : SpectraShadow 𝕋 N := T.absorb
  { k := T'.k + (N + 1)
    m := 1 + T'.m + 1
    A₀ := fun _ _ => zero
    A := Fin.append
      (Fin.append (fun _ => blockDiag zero T'.A₀ (arrowMat one zero T'.c))
        (fun j => blockDiag zero (T'.A j) (arrowMat zero zero (T'.G j))))
      (fun _ => blockDiag zero (fun _ _ => zero) (arrowMat zero one (fun _ => zero)))
    c := fun _ => zero
    G := Fin.append (Fin.append (fun _ => T'.c) T'.G) (fun _ _ => zero)
    E := Interval.origin N }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

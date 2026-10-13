import CORALean.ContSet.ZonoBundle.Float.Operations.Enlarge
import CORALean.ContSet.ContSet.Theorems.EnlargeScalarOuter

/-!
# Each member of a float enlarged bundle encloses the scaling of its own member

Per member, as over ℝ: the image of member `i` under `x ↦ cᵢ + f ⊙ (x - cᵢ)` (the centre and `f`
as the floats read) lies in member `i` of the result, and the result is the intersection of those
members (`construct_enlarge`). Nothing is claimed for the image of the intersection.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.enlarge_outer (zB : ZonoBundle (Vec 𝕋 n)) (f : Vec 𝕋 n) (i : Fin zB.k) :
    (fun x : Vec ℝ n =>
        toRealVec (ScalarCentre.centreVec (𝕋 := 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) (zB.Z i)) +
          fun j => toReal (f j) *
            (x j - toRealVec (ScalarCentre.centreVec (𝕋 := 𝕋) (S := fun k => Zonotope (Vec 𝕋 k))
              (zB.Z i)) j)) ''
      (zB.Z i).construct ⊆ ((zB.enlarge f).Z i).construct :=
  ContSet.enlargeScalar_outer (S := fun k => Zonotope (Vec 𝕋 k)) (𝕋 := 𝕋) (zB.Z i) f

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ZonoBundle.Float.Operations.Enlarge
public import CORALean.ContSet.ContSet.Theorems.EnlargeScalarOuter

@[expose] public section

/-!
# Each member of a float enlarged bundle encloses the scaling of its own member

Per member, as over ℝ: the image of member `i` under `x ↦ cᵢ + f ⊙ (x - cᵢ)` (the center and `f`
as the floats read) lies in member `i` of the result, and the result is the intersection of those
members (`construct_enlarge`). Nothing is claimed for the image of the intersection.

## Inputs
* `zB` – float zonotope bundle
* `f` – enlargement factor per coordinate
* `i` – member index

## Hypotheses
* none

## Conclusion
* the scaling of member i is contained in the enlarged member
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

theorem ZonoBundle.enlarge_outer (zB : ZonoBundle (Vec 𝕋 n)) (f : Vec 𝕋 n)
    (i : Fin zB.k) :
    (fun x : Vec ℝ n =>
        toRealVec (ScalarCenter.centerVec (𝕋 := 𝕋) (S := 𝒵[𝕋]) (zB.Z i)) +
          fun j => toReal (f j) *
            (x j - toRealVec (ScalarCenter.centerVec (𝕋 := 𝕋) (S := 𝒵[𝕋])
              (zB.Z i)) j)) ''
      (zB.Z i).construct ⊆ ((zB.enlarge f).Z i).construct :=
  ContSet.enlargeScalar_outer (S := 𝒵[𝕋]) (𝕋 := 𝕋) (zB.Z i) f

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

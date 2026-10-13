module

public import CORALean.ContSet.Zonotope.Float.Operations.Rotate
public import CORALean.ContSet.Zonotope.Float.Theorems.RotMatMem
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter

@[expose] public section

/-!
# Rotating a float zonotope encloses the rotated set

The rotation at the float angle lies in the interval `rotMat` (`rotMat_mem`), and
`mtimesIntervalMat` encloses the image under every matrix of that interval.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.rotate_outer (p : ℕ) {n : ℕ} (Z : Zonotope (Vec 𝕋 n)) (i j : Fin n) (angle : 𝕋) :
    (Real.rotMat n i j (toReal angle) *ᵥ ·) '' Z.construct ⊆
      (Zonotope.rotate p Z i j angle).construct := fun _ hy =>
  Zonotope.mtimesIntervalMat_outer _ Z (Set.mem_biUnion (rotMat_mem p n i j angle) hy)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

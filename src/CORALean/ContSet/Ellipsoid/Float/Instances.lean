import CORALean.ContSet.Ellipsoid.Float.Theorems.MtimesOuter

/-!
# What `Ellipsoid` instantiates

`Mtimes`, and deliberately nothing else — the same one the exact layer
instantiates, and for the same reason: an ellipsoid is closed under a linear
image and under nothing else the interface names, and every enclosure of a sum,
a combination or a reduction carries a free parameter a class field has no room
for.

`ContSet` is not among them: `InflatedContSet` supplies it, which is what makes
this the same interface as over ℝ.

`plus` is here as an operation and is not an instance, exactly as over ℝ. Its
free parameter is now two floats and a certificate rather than one real `l`,
which is a stronger reason for the same choice, not a weaker one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

instance : Mtimes (Mat 𝕋) (Ellipsoid 𝕋) where
  mtimes := Ellipsoid.mtimes
  mtimes_outer M E := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton]
    exact Ellipsoid.mtimes_outer M E

end CORALean.Float

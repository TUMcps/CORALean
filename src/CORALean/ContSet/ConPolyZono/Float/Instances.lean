import CORALean.ContSet.ConPolyZono.Float.Theorems.MtimesOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.PlusOuter

/-!
# What `ConPolyZono` instantiates

`Plus` and `Mtimes`, as over ℝ. `ContSet` is not among them —
`InflatedContSet` supplies it, which is what makes this the same class the exact
layer instantiates.

`and` is computed here but instantiates nothing, exactly as over ℝ: there is no
`And` class to instantiate, and a class one or two representations implement is
a name rather than an interface. A caller names `ConPolyZono.and`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

instance {n : ℕ} : Plus (ConPolyZono 𝕋 n) (Vec ℝ n) where
  plus := ConPolyZono.plus
  plus_outer := ConPolyZono.plus_outer

instance : Mtimes (Mat 𝕋) (ConPolyZono 𝕋) where
  mtimes := ConPolyZono.mtimes
  mtimes_outer M C := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton]
    exact ConPolyZono.mtimes_outer M C

end CORALean.Float

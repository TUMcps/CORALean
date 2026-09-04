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
  plus C₁ C₂ := (C₁.plus C₂).materialise
  plus_outer C₁ C₂ := by
    rw [ConPolyZono.materialise_eq]
    exact ConPolyZono.plus_outer C₁ C₂

instance : Mtimes (Mat 𝕋) (ConPolyZono 𝕋) where
  mtimes M C := (ConPolyZono.mtimes M C).materialise
  mtimes_outer M C := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, ConPolyZono.materialise_eq]
    exact ConPolyZono.mtimes_outer M C

end CORALean.Float

import CORALean.ContSet.ConPolyZono.Float.Theorems.MtimesOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.PlusOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceOuter

/-!
# What `ConPolyZono` instantiates

`Plus`, `Mtimes` and `Reduce`, as over ℝ. `ContSet` is not among them —
`InflatedContSet` supplies it, which is what makes this the same class the exact
layer instantiates.

`Reduce` is *computable* here where the exact layer's instance is not:
`Tuple.sort` needs a `LinearOrder`, which no float type has lawfully, while
`sortPerm` asks its comparator for nothing. Soundness never depended on the
ranking — `reduceBy_outer` holds at every partition — so the free comparator
costs precision and nothing else. No `CompactSet`, as at no other float
representation: compactness is a statement about the exact specification.

`and` is computed here but instantiates nothing, exactly as over ℝ: there is no
`And` class to instantiate, and a class one or two representations implement is
a name rather than an interface. A caller names `ConPolyZono.and`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

instance {n : ℕ} : Plus (ConPolyZono 𝕋 n) (Vec ℝ n) where
  plus C₁ C₂ := (C₁.plus C₂).materialise
  plus_outer C₁ C₂ := by
    rw [ConPolyZono.materialise_eq]
    exact ConPolyZono.plus_outer C₁ C₂

-- `reduce` is computable here, `sortPerm` asking its comparator for no laws
instance {n : ℕ} : Reduce (ConPolyZono 𝕋 n) (Vec ℝ n) where
  reduce C o := (C.reduce o).materialise
  reduce_outer C o := by
    rw [ConPolyZono.materialise_eq]
    exact ConPolyZono.reduce_outer C o

instance : Mtimes (Mat 𝕋) (ConPolyZono 𝕋) where
  mtimes M C := (ConPolyZono.mtimes M C).materialise
  mtimes_outer M C := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, ConPolyZono.materialise_eq]
    exact ConPolyZono.mtimes_outer M C

end CORALean.Float

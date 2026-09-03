import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReindexExact

/-!
# What `Zonotope` instantiates

`ContSet` is not among them — `InflatedContSet` supplies it, which is what makes
this the same class the exact layer instantiates. So an algorithm written against
the three operation classes run here with no float counterpart to write.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

instance {n : ℕ} : Plus (Zonotope 𝕋 n) (Vec ℝ n) where
  plus := Zonotope.plus
  plus_outer := Zonotope.plus_outer

instance {n : ℕ} : LinComb (Zonotope 𝕋 n) (Vec ℝ n) where
  linComb := Zonotope.linComb
  linComb_outer := Zonotope.linComb_outer

instance {n : ℕ} : Reduce (Zonotope 𝕋 n) (Vec ℝ n) where
  reduce := Zonotope.reduce
  reduce_outer := Zonotope.reduce_outer

/-- Exact, alone among the fields here: a relabelling moves stored floats and
computes nothing, so the error box is carried across rather than grown. -/
instance : Reindex (Zonotope 𝕋) where
  reindex := Zonotope.reindex
  reindex_exact := Zonotope.reindex_exact

instance : Mtimes (Mat 𝕋) (Zonotope 𝕋) where
  mtimes := Zonotope.mtimes
  mtimes_outer M Z := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton]
    exact Zonotope.mtimes_outer M Z

end CORALean.Float

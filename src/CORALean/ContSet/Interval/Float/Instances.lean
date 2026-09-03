import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.ReindexExact

/-!
# What `Interval` instantiates

The same obligations the exact layer discharges, since a float interval denotes a
set of real points just as an exact one does; only the scalar the operations run
in differs.

`reduce` is the identity, as over ℝ: an interval has no order to give up.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

instance : ContSet (Interval 𝕋 n) (Vec ℝ n) := ⟨Interval.construct⟩

instance : Plus (Interval 𝕋 n) (Vec ℝ n) where
  plus := Interval.plus
  plus_outer := Interval.plus_outer

instance : LinComb (Interval 𝕋 n) (Vec ℝ n) where
  linComb := Interval.linComb
  linComb_outer := Interval.linComb_outer

instance : Reduce (Interval 𝕋 n) (Vec ℝ n) where
  reduce I _ := I
  reduce_outer _ _ := subset_rfl

/-- The one field here that is an equality: a relabelling does no arithmetic, so
the float box loses exactly what the exact one does, namely nothing. -/
instance : Reindex (Interval 𝕋) where
  reindex := Interval.reindex
  reindex_exact := Interval.reindex_exact

instance : Mtimes (Mat 𝕋) (Interval 𝕋) where
  mtimes := Interval.mtimes
  mtimes_outer M I := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton]
    exact Interval.mtimes_outer M I

end CORALean.Float

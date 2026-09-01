import CORALean.ContSet.Interval.Float.Theorems.API

/-!
# What `Interval` instantiates

The same obligations the exact layer discharges, since a float interval denotes a
set of real points just as an exact one does; only the scalar the operations run
in differs.

`reduce` is the identity, as over ℝ: an interval has no order to give up.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

instance : ContSet (Interval 𝕋 n) (Vec ℝ n) := ⟨Interval.construct⟩

instance : OuterContSet (Interval 𝕋 n) (Vec ℝ n) where
  plus := Interval.plus
  linComb := Interval.linComb
  reduce I _ := I
  plus_outer := Interval.plus_outer
  linComb_outer := Interval.linComb_outer
  reduce_outer _ _ := subset_rfl

instance : Mtimes (Mat 𝕋) (Interval 𝕋) where
  mtimes := Interval.mtimes
  mtimes_outer M I := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton]
    exact Interval.mtimes_outer M I

end CORALean.Float

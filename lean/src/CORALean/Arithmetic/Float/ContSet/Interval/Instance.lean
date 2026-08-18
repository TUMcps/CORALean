import CORALean.Arithmetic.Float.ContSet.Interval.Theorems

/-!
# What `Interval` instantiates

The class fields *are* the obligations, so there is nothing to restate. They are
the exact layer's, because a float interval denotes a set of real points just as
an exact one does; only the scalar the operations run in differs.

`reduce` is the identity, as over ℝ: an interval has no order to give up.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

instance : Real.ContSet (Interval 𝕋 n) n := ⟨Interval.construct⟩

instance : Real.OuterContSet (Interval 𝕋) 𝕋 where
  plus := Interval.plus
  mtimes := Interval.mtimes
  reduce I _ := I
  plus_outer := Interval.plus_outer
  mtimes_outer := Interval.mtimes_outer
  reduce_outer _ _ := subset_rfl

end CORALean.Arithmetic.Float

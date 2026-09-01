import CORALean.ContSet.Interval.Real.Theorems.API

/-!
# What `Interval` instantiates

`reduce` is the identity: an interval holds two bounds per coordinate whatever
order is asked for, so it has nothing to give up.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- At every ambient type that has coordinates, so an interval matrix is an
instance too. The `OuterContSet` instance below is stated only at `Vec`, which
is where an algorithm asks for it. -/
instance {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι] :
    ContSet (Interval α) α := ⟨Interval.construct⟩

instance : OuterContSet (Interval (Vec ℝ n)) (Vec ℝ n) where
  plus := Interval.plus
  linComb := Interval.linComb
  reduce I _ := I
  plus_outer := Interval.plus_outer
  linComb_outer := Interval.linComb_outer
  reduce_outer _ _ := subset_rfl

instance : Mtimes (Mat ℝ) (fun n => Interval (Vec ℝ n)) where
  mtimes := Interval.mtimes
  mtimes_outer M I := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Interval.mtimes_outer M I

/-- The interval-matrix family. A generic theorem quantifies over `𝕄 : ℕ → ℕ → Type`
and the elaborator cannot read that family off one member, so a use site has to
name it: `(𝕄 := ℐ)`. -/
scoped notation "ℐ" => fun m n => Interval (Mat ℝ m n)

end CORALean.Real

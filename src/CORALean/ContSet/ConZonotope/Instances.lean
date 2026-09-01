import CORALean.ContSet.ConZonotope.Theorems.API

/-!
# What `ConZonotope` instantiates

Noncomputable, as `reduce` is: it ranks generators, and ordering reals cannot be
computed.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- At every ambient type, not only `Vec`: the constraints live on the
coefficient space whatever the generators point into. -/
instance {α : Type} [AddCommGroup α] [Module ℝ α] : ContSet (ConZonotope α) α :=
  ⟨ConZonotope.construct⟩

noncomputable instance : OuterContSet (ConZonotope (Vec ℝ n)) (Vec ℝ n) where
  plus := ConZonotope.plus
  linComb := ConZonotope.linComb
  reduce := ConZonotope.reduce
  plus_outer C₁ C₂ := (ConZonotope.plus_exact C₁ C₂).subset
  linComb_outer := ConZonotope.linComb_outer
  reduce_outer := ConZonotope.reduce_outer

instance : Mtimes (Mat ℝ) (fun n => ConZonotope (Vec ℝ n)) where
  mtimes := ConZonotope.mtimes
  mtimes_outer M C := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (ConZonotope.mtimes_exact M C).subset

end CORALean.Real

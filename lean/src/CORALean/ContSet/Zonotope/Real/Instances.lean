import CORALean.ContSet.Zonotope.Real.Theorems.API

/-!
# What `Zonotope` instantiates

The class fields *are* the obligations, so there is nothing to restate. Each is a
theorem from `Theorems`: the two exact ones give their `⊆` direction, and
`reduce_outer` is already one.

Noncomputable, as `reduce` is: it ranks generators, and ordering reals cannot be
computed.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

instance : ContSet (Zonotope (Vec ℝ n)) (Vec ℝ n) := ⟨Zonotope.construct⟩

noncomputable instance : OuterContSet (Zonotope (Vec ℝ n)) (Vec ℝ n) where
  plus := Zonotope.plus
  linComb := Zonotope.linComb
  reduce := Zonotope.reduce
  plus_outer Z₁ Z₂ := (Zonotope.plus_exact Z₁ Z₂).subset
  linComb_outer := Zonotope.linComb_outer
  reduce_outer := Zonotope.reduce_outer

instance : Mtimes (Mat ℝ) (fun n => Zonotope (Vec ℝ n)) where
  mtimes := Zonotope.mtimes
  mtimes_outer M Z := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (Zonotope.mtimes_exact M Z).subset

/-- The same operation at an interval matrix, which `OuterContSet` does not ask
for: a zonotope carries it, and a discretization is what wants it. -/
noncomputable instance : Mtimes IntervalMat (fun n => Zonotope (Vec ℝ n)) where
  mtimes := Zonotope.mtimesIntervalMat
  mtimes_outer IM Z := by
    simp only [IntervalMat.construct_eq]
    exact Zonotope.mtimesIntervalMat_outer IM Z

end CORALean.Real

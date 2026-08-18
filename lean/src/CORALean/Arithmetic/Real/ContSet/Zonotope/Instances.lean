import CORALean.Arithmetic.Real.ContSet.Zonotope.Theorems.API

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

namespace CORALean.Arithmetic.Real

open Matrix

variable {n : ℕ}

instance : ContSet (Zonotope n) n := ⟨Zonotope.construct⟩

noncomputable instance : OuterContSet Zonotope ℝ where
  plus := Zonotope.plus
  mtimes := Zonotope.mtimes
  reduce := Zonotope.reduce
  plus_outer Z₁ Z₂ := (Zonotope.plus_exact Z₁ Z₂).subset
  mtimes_outer M Z := by
    simp only [MatSet.denote_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (Zonotope.mtimes_exact M Z).subset
  reduce_outer := Zonotope.reduce_outer

/-- What a time-interval enclosure needs, and `OuterContSet` does not ask for. -/
noncomputable instance : LinComb Zonotope where
  linComb := Zonotope.linComb
  linComb_outer := Zonotope.linComb_outer

/-- The same operation at an interval matrix, which `OuterContSet` does not ask
for: a zonotope carries it, and a discretization is what wants it. -/
noncomputable instance : Mtimes IntervalMat Zonotope where
  mtimes := Zonotope.mtimesIntervalMat
  mtimes_outer IM Z := by
    simp only [IntervalMat.denote_eq]
    exact Zonotope.mtimesIntervalMat_outer IM Z

end CORALean.Arithmetic.Real

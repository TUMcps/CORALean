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
  mtimes_outer M Z := (Zonotope.mtimes_exact M Z).subset
  reduce_outer := Zonotope.reduce_outer

end CORALean.Arithmetic.Real

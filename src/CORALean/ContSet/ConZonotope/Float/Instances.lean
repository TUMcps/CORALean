import CORALean.ContSet.ConZonotope.Float.Theorems.API

/-!
# What the float `ConZonotope` instantiates

The three operation classes. `Mtimes` waits on `mtimes`, which waits on the
float zonotope's rounding argument being factored so it can be reused rather
than copied.

No `Intersection`, unlike the exact layer: nothing here computes a constrained
zonotope's intersection, so there is no `intersection` to wire — a fresh operation, out
of scope here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

/-- The one computable field here, and so the only one storage can reach: the two
below go through a linear program and are `noncomputable`. -/
instance : Plus (ConZonotope 𝕋 n) (Vec ℝ n) where
  plus C₁ C₂ := (C₁.plus C₂).materialise
  plus_outer C₁ C₂ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.plus_outer C₁ C₂

noncomputable instance : LinComb (ConZonotope 𝕋 n) (Vec ℝ n) where
  linComb := ConZonotope.linComb
  linComb_outer := ConZonotope.linComb_outer

noncomputable instance : Reduce (ConZonotope 𝕋 n) (Vec ℝ n) where
  reduce := ConZonotope.reduce
  reduce_outer := ConZonotope.reduce_outer

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

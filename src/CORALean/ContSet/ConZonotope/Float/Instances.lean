import CORALean.ContSet.ConZonotope.Float.Theorems.API

/-!
# What the float `ConZonotope` instantiates

The three operation classes, then `Reindex`, which is exact. `Mtimes` waits on `mtimes`,
which waits on the
float zonotope's rounding argument being factored so it can be reused rather
than copied.

No `Intersection`, unlike the exact layer: nothing here computes a constrained
zonotope's intersection, so there is no `intersection` to wire — a fresh operation, out
of scope here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   08-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : Plus (ConZonotope 𝕋 n) (Vec ℝ n) where
  plus C₁ C₂ := (C₁.plus C₂).materialise
  plus_outer C₁ C₂ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.plus_outer C₁ C₂

instance : LinComb (ConZonotope 𝕋 n) (Vec ℝ n) where
  linComb := ConZonotope.linComb
  linComb_outer := ConZonotope.linComb_outer

instance : Reduce (ConZonotope 𝕋 n) (Vec ℝ n) where
  reduce := ConZonotope.reduce
  reduce_outer := ConZonotope.reduce_outer

/-- Exact, alone among the fields here: a relabelling moves stored floats and
computes nothing, so the error box is carried across rather than grown. -/
instance : Reindex (ConZonotope 𝕋) where
  reindex e cZ := (ConZonotope.reindex e cZ).materialise
  reindex_exact e cZ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.reindex_exact e cZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

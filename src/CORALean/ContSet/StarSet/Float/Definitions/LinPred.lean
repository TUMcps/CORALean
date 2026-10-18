module

public import CORALean.Global.Tensor

@[expose] public section

/-!
# CORA's star-set predicate over a floating-point scalar

`Real.StarSet.LinPred` with its numbers stored in `𝕋`: the rows `(a, b)`, `a · α ≤ b`, as a list,
and the box `[l, u]` of the coefficients. Its own file because the float star set is stated with
it, and its exact reading, `nominal`, is in the file of the star set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- CORA's predicate `C α ≤ d, l ≤ α ≤ u` stored in `𝕋`: the rows and the box. -/
structure StarSet.LinPred (𝕋 : Type) (m : ℕ) where
  cons : List ((Fin m → 𝕋) × 𝕋)
  l : Fin m → 𝕋
  u : Fin m → 𝕋

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

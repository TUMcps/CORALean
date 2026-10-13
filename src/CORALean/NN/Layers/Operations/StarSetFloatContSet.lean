module

public import CORALean.NN.Layers.Definitions.StarSetFloat

@[expose] public section

/-!
# The denotation of a float star set

What the stored numbers read as reals denote: the points `c + G α` over the factors `α` in the
box `[l, u]` with every row satisfied. A float step is sound when the real image of the set lies
in the denotation of the set it returns.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet Float.SoundFloatArithmetic


-- ======================================  MAIN INSTANCE  ======================================= --

/-- The points of the star set, read as reals. -/
instance {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] (n : ℕ) :
    ContSet (StarSet 𝕋 n) (Vec ℝ n) where
  construct s := {x | ∃ α : Fin s.m → ℝ, (∀ k, toReal (s.l k) ≤ α k ∧ α k ≤ toReal (s.u k)) ∧
    (∀ r ∈ s.cons, ∑ k, toReal (r.1 k) * α k ≤ toReal r.2) ∧
    ∀ i, x i = toReal (s.c i) + ∑ k, toReal (s.G i k) * α k}

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

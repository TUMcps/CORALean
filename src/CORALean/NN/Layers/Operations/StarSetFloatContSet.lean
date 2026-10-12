import CORALean.NN.Layers.Definitions.StarSetFloat

/-!
# The denotation of a float star set

What the stored numbers read as reals denote: the points `c + G α` over the factors `α` in the
box `[l, u]` with every row satisfied. A float step is sound when the real image of the set lies
in the denotation of the set it returns.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float.SoundFloatArithmetic


-- ======================================  MAIN INSTANCE  ======================================= --

/-- The points of the star set, read as reals. -/
instance {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] (n : ℕ) :
    ContSet (StarSetFloat 𝕋 n) (Vec ℝ n) where
  construct s := {x | ∃ α : Fin s.m → ℝ, (∀ k, toReal (s.l k) ≤ α k ∧ α k ≤ toReal (s.u k)) ∧
    (∀ r ∈ s.cons, ∑ k, toReal (r.1 k) * α k ≤ toReal r.2) ∧
    ∀ i, x i = toReal (s.c i) + ∑ k, toReal (s.G i k) * α k}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

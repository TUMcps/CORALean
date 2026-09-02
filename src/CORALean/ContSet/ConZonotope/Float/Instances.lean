import CORALean.ContSet.ConZonotope.Float.Theorems.API

/-!
# What the float `ConZonotope` instantiates

The three operation classes. `Mtimes` waits on `mtimes`, which waits on the
float zonotope's rounding argument being factored so it can be reused rather
than copied.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

instance : Plus (ConZonotope 𝕋 n) (Vec ℝ n) where
  plus := ConZonotope.plus
  plus_outer := ConZonotope.plus_outer

noncomputable instance : LinComb (ConZonotope 𝕋 n) (Vec ℝ n) where
  linComb := ConZonotope.linComb
  linComb_outer := ConZonotope.linComb_outer

noncomputable instance : Reduce (ConZonotope 𝕋 n) (Vec ℝ n) where
  reduce := ConZonotope.reduce
  reduce_outer := ConZonotope.reduce_outer

end CORALean.Float

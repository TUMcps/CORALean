module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.HPolytope.Float.Operations.RowLin
public import CORALean.Global.Float.FloatBound

@[expose] public section

/-!
# `HPolytope.minkDiffOf`

CORA's `@polytope/minkDiff` over a floating-point scalar, as the exact layer has
it: each inequality row shifts inward by the subtrahend's support in that row's
own direction, and the equality rows are copied unchanged.

The support bounds are certificates, `FloatBound`s against the rows the stored
matrix denotes, as `plusOf` takes them. The one subtraction rounds downward:
a difference is a guarantee, so the shifted bound may only come out smaller,
never larger, and the result stays inside the exact difference.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.minkDiffOf (P : HPolytope 𝕋 (Vec 𝕋 n)) (T : Set (Vec ℝ n))
    (u : ∀ i, FloatBound 𝕋 T (rowLin P.A i)) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := P.m
  A := P.A
  b := fun i => subDown (P.b i) (u i).val
  me := P.me
  Ae := P.Ae
  be := P.be

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

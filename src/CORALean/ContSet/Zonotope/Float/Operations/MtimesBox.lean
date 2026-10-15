module

public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

@[expose] public section

/-!
# `Zonotope.mtimesBox`

A box that holds everything `mtimes M Z` may contain beyond `M` applied to `Z`.

The float `mtimes` rounds the center and every generator of the result. This box collects
those rounding errors. It adds up three parts.

* The rounding error of the new center, bounded as in `plusBox`.
* The rounding error of the new generators. Each entry is off by at most `matMulDiff`, and
  `generatorError` turns these bounds into a box, as `mtimesResidual` does.
* The error box of `mtimes M Z`.

It is computed in `𝕋` with directed rounding. It is not a reduction, for the reason `plusBox`
is not: only the definition of `mtimes` says how far the result can stray from `M Z`.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       08-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Input: a matrix `M` and a zonotope `Z`. Output: a box holding the rounding errors of
`mtimes M Z`, the sum of the three parts named in the module docstring. -/
def Zonotope.mtimesBox (M : Mat 𝕋 m n) (Z : Zonotope (Vec 𝕋 n)) : Interval (Vec 𝕋 m) :=
  (⟨fun i => subDown (mulVecDown M Z.c i) (mulVecUp M Z.c i), fun _ => zero⟩ :
      Interval (Vec 𝕋 m)).plus
    ((Zonotope.generatorError (matMulDiff M fun i j => Z.G j i)).plus
      (Zonotope.mtimes M Z).I_error)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

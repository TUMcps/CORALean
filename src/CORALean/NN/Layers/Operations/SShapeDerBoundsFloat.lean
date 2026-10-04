import CORALean.NN.Layers.Operations.SShapeDerBounds
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `nnSShapeLayer.getDerBounds` in floats

CORA's `getDerBounds` [1]: the least and greatest derivative of an S-shaped activation over
`[l, u]`, from float bounds `dfLo`, `dfHi` of the derivative at a stored point. The least value is
at the end farther from `0`, so the lesser of the two ends; the greatest is `df 0` where `0` lies
inside, and the nearer end otherwise. A float comparison is only trusted when it answers `true`,
so where neither side of `0` is certified the peak `df 0`, a bound everywhere, is returned: wider
than CORA's three cases there, never narrower. Not modelled, as at ℝ: the `NaN` fallback.

## References

* [1] `nn/@nnSShapeLayer/getDerBounds.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bounds `(df_l, df_u)` on `df` over `[l, u]`, from float bounds of `df` at stored points. -/
def sShapeDerBoundsFloat (dfLo dfHi : 𝕋 → 𝕋) (l u : 𝕋) : 𝕋 × 𝕋 :=
  (minimum (dfLo l) (dfLo u),                                       -- the farther end
   if le l zero && le zero u then dfHi zero                         -- `0` inside: the peak
   else if le zero l then dfHi l                                    -- right of `0`: decreasing
   else if le u zero then dfHi u                                    -- left of `0`: increasing
   else dfHi zero)                                                  -- undecided: the peak

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

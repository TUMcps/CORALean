module

public import CORALean.ContDynamics.NonlinearARX.NonlinearARX
public import CORALean.ContSet.Interval.Float.Instances

@[expose] public section

/-!
# What a float run is told about a nonlinear ARX model

`NonlinearARX` stores `f_ARX` over ℝ, which no float run can evaluate. A `FloatModel` is what
it evaluates instead: an interval extension of `f_ARX` over a box of past outputs and a box of
the stacked inputs, as a computable function at the scalar `𝕋`. `Encloses` ties it to `f_ARX`,
beside the structure rather than inside it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- An interval extension of `f_ARX`. -/
structure NonlinearARX.FloatModel (𝕋 : Type) (dy du p : ℕ) where
  f : Interval (Vec 𝕋 (p * dy)) → Interval (Vec 𝕋 ((p + 1) * du)) → Interval (Vec 𝕋 dy)

/-- `fm` encloses `sys`: its value over two boxes contains `f_ARX` at every point of them. -/
structure NonlinearARX.FloatModel.Encloses (fm : NonlinearARX.FloatModel 𝕋 dy du p)
    (sys : NonlinearARX dy du p) : Prop where
  f_mem (Y : Interval (Vec 𝕋 (p * dy))) (V : Interval (Vec 𝕋 ((p + 1) * du))) :
    ∀ y ∈ construct Y, ∀ v ∈ construct V, sys.f y v ∈ construct (fm.f Y V)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

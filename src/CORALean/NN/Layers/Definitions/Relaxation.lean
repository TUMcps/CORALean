import CORALean.Global.Float.SoundFloatArithmetic

/-!
# What an activation function has to supply

An activation layer applies one scalar function `σ` to every neuron, and no representation is
closed under one, so the layer is an enclosure and a `Relaxation` is what makes it a sound one:
per neuron, an affine map `slope · t + offset` and the `error` to allow for, all functions of
the neuron's bounds `[l, u]` and stored in the scalar `𝕋`. ReLU has no affine enclosure with a
finite error on all of ℝ, which is why they are functions of the bounds.

`Sound` is what ties a relaxation to `σ`, split off so that nothing compiled mentions ℝ: it is
an *inequality* against `error`, measured from the values actually stored, so a slope and an
offset computed in any precision are sound as they stand and only `error` has to grow. At
`𝕋 := ℝ` every rounding is exact and this is CORA's relaxation as printed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- An affine map per box, stored in the scalar and nothing else. -/
structure Relaxation (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] where
  slope : 𝕋 → 𝕋 → 𝕋
  offset : 𝕋 → 𝕋 → 𝕋
  error : 𝕋 → 𝕋 → 𝕋

/-- That it encloses `σ` on every box the stored values describe. The bounds arrive in `𝕋` and
the argument stays real: what the layer encloses is the exact function. -/
structure Relaxation.Sound (R : Relaxation 𝕋) (σ : ℝ → ℝ) : Prop where
  sound {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    |σ t - (toReal (R.slope l u) * t + toReal (R.offset l u))| ≤ toReal (R.error l u)

/-- `Sound`, asked only of the boxes `P` holds on: for a function a machine enclosure can bracket
only where its argument is bounded, as `exp` is by `Float.expUp`. -/
structure Relaxation.SoundWhere (R : Relaxation 𝕋) (σ : ℝ → ℝ) (P : 𝕋 → 𝕋 → Prop) : Prop where
  sound {l u : 𝕋} {t : ℝ} (hP : P l u) (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    |σ t - (toReal (R.slope l u) * t + toReal (R.offset l u))| ≤ toReal (R.error l u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

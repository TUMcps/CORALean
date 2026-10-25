module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# What an activation function has to supply

An activation layer applies one scalar function `σ` to every neuron, and no representation is closed
under one, so a `Relaxation` is what makes the layer a sound enclosure: per neuron, an affine map
`slope · t + offset` and the `error` to allow for, all functions of the neuron's bounds `[l, u]` and
stored in `𝕋` (ReLU has no affine enclosure with finite error on all of ℝ). `IsSound` ties it to
`σ`, split off so nothing compiled mentions ℝ: an *inequality* against `error` from the values
actually stored, so a slope and offset computed in any precision are sound as they stand and only
`error` grows. At `𝕋 := ℝ` this is CORA's relaxation as printed.

-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


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
structure Relaxation.IsSound (R : Relaxation 𝕋) (σ : ℝ → ℝ) : Prop where
  sound {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    |σ t - (toReal (R.slope l u) * t + toReal (R.offset l u))| ≤ toReal (R.error l u)

/-- `IsSound`, asked only of the boxes `P` holds on: for a function a machine enclosure can bracket
only where its argument is bounded, as `exp` is by `Float.expUp`. -/
structure Relaxation.IsSoundWhere (R : Relaxation 𝕋) (σ : ℝ → ℝ) (P : 𝕋 → 𝕋 → Prop) : Prop where
  sound {l u : 𝕋} {t : ℝ} (hP : P l u) (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    |σ t - (toReal (R.slope l u) * t + toReal (R.offset l u))| ≤ toReal (R.error l u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

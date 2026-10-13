import CORALean.Global.Float.Instances.Real.Instances

/-!
# A function bracketed at every stored value

`FloatOps` evaluates no transcendental function, so a relaxation that needs `σ` at the ends
of a box — the slope-zero one of a monotone `σ`, the curvature-based ones — needs it handed
in: a lower and an upper value at every stored argument. `Global/Float/Exp` builds such a pair
for the exponential. `Sound` is that the two bracket `σ`, split off as for `Relaxation`. At
`𝕋 := ℝ` the exact enclosure is `σ` itself at both ends, which is how an exact relaxation is
built from the same constructors a machine scalar runs.
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

/-- A machine enclosure at a stored value, which is what a slope-zero relaxation needs. -/
structure Enclosure (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] where
  lo : 𝕋 → 𝕋
  hi : 𝕋 → 𝕋

/-- That the two ends bracket `σ` at every stored value. -/
structure Enclosure.Sound (E : Enclosure 𝕋) (σ : ℝ → ℝ) : Prop where
  lo_le (a : 𝕋) : toReal (E.lo a) ≤ σ (toReal a)
  le_hi (a : 𝕋) : σ (toReal a) ≤ toReal (E.hi a)

/-- `σ` itself at both ends, which only ℝ stores. -/
noncomputable def Enclosure.exact (σ : ℝ → ℝ) : Enclosure ℝ := ⟨σ, σ⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Capsule.Float.Operations.PiStep

@[expose] public section

/-!
# `Capsule.piStep` brackets `π / 499`

The two ends of `piStep` are bounds of the real `π / 499`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.piStep_mem (p k : ℕ) :
    toReal (Capsule.piStep (𝕋 := 𝕋) p k).1 ≤ Real.pi / 499 ∧
      Real.pi / 499 ≤ toReal (Capsule.piStep (𝕋 := 𝕋) p k).2 := by -- --- PROOF ---
  have hm : toReal (acosDown p k (zero : 𝕋)) ≤ Real.pi / 2 := by
    have := acosDown_le p k (zero : 𝕋)
    rwa [toReal_zero, Real.arccos_zero] at this
  have hp : Real.pi / 2 ≤ toReal (acosUp p k (zero : 𝕋)) := by
    have := le_acosUp p k (zero : 𝕋)
    rwa [toReal_zero, Real.arccos_zero] at this
  have hpi := Real.pi_pos
  -- the divisors: `499` between `intDown` and `intUp`
  have hu : (499 : ℝ) ≤ toReal (intUp 499 : 𝕋) := by
    have := (intDown_le_intUp (𝕋 := 𝕋) 499).2
    simpa using this
  have hd : toReal (intDown 499 : 𝕋) ≤ 499 := by
    have := (intDown_le_intUp (𝕋 := 𝕋) 499).1
    simpa using this
  have hLo := addDown_le_add (acosDown p k (zero : 𝕋)) (acosDown p k zero)
  have hHi := add_le_addUp (acosUp p k (zero : 𝕋)) (acosUp p k zero)
  unfold Capsule.piStep
  dsimp only
  constructor
  · -- from below: the quotient by a divisor at least `499`
    refine le_trans (divDown_le_div _ _ (by linarith)) ?_
    by_cases h : toReal (addDown (acosDown p k (zero : 𝕋)) (acosDown p k zero)) ≤ 0
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg h (by linarith)) (by positivity)
    · push Not at h
      exact le_trans (div_le_div_of_nonneg_left h.le (by norm_num) hu)
        (div_le_div_of_nonneg_right (by linarith) (by norm_num))
  · split_ifs with hc
    · -- from above: the divisor positive and at most `499`
      have hpos : 0 < toReal (intDown 499 : 𝕋) := by
        simpa [toReal_zero] using toReal_lt_of_ltStrict hc
      refine le_trans ?_ (div_le_divUp _ _ hpos)
      exact le_trans (div_le_div_of_nonneg_right (by linarith) (by norm_num))
        (div_le_div_of_nonneg_left (by linarith) hpos hd)
    · -- no certified divisor: `π / 499 ≤ π`
      linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

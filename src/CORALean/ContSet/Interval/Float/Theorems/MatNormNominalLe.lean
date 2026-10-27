module

public import CORALean.ContSet.Interval.Float.Theorems.MatNormLe
public import CORALean.ContSet.Interval.Real.Theorems.MatNormIsGreatest

@[expose] public section

/-!
# `Interval.matNorm` bounds the exact layer's `matNorm`

For a nonempty box the exact layer's `matNorm` is the greatest norm over the members and is
attained, so the member bound `matNorm_le` gives the float norm as an upper bound of it.

## Inputs
* `steps` – number of Newton steps of the square root
* `p` – norm type
* `I` – interval matrix

## Hypotheses
* `hI` – the stored bounds are ordered entrywise

## Conclusion
* the exact layer's norm is at most the float norm
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.matNorm_nominal_le (steps : ℕ) (p : Real.Interval.NormType)
    (I : Interval (Mat 𝕋 m n))
    (hI : ∀ i j, toReal (I.inf i j) ≤ toReal (I.sup i j)) :
    Real.Interval.matNorm p I.nominal ≤ toReal (I.matNorm steps p) := by
  -- the exact norm is attained by a member, which `matNorm_le` bounds
  obtain ⟨⟨M, hM, hMeq⟩, -⟩ := Real.Interval.matNorm_isGreatest p I.nominal hI
  rw [← hMeq]
  exact Interval.matNorm_le steps p I hM

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

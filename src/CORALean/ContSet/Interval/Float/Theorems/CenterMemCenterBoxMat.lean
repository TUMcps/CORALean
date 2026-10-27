module

public import CORALean.ContSet.Interval.Float.Operations.CenterBoxMat
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# The real midpoint lies in `Interval.centerBoxMat`

The sum is rounded down for the lower end and up for the upper, and `half` is exact, so the real
midpoint of the stored bounds is bracketed entry by entry.

## Inputs
* `I` – interval matrix

## Hypotheses
* none

## Conclusion
* the midpoint of the nominal interval matrix lies in the box
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

theorem Interval.center_mem_centerBoxMat (I : Interval (Mat 𝕋 m n)) : -- --- CONCL ---
    I.nominal.center ∈ I.centerBoxMat.construct := by -- --- PROOF ---
  intro q
  obtain ⟨i, j⟩ := q
  have h : I.nominal.center i j = (toReal (I.inf i j) + toReal (I.sup i j)) / 2 := by
    show (2:ℝ)⁻¹ * (toReal (I.inf i j) + toReal (I.sup i j)) = _
    ring
  simp only [Entrywise.entry_mat]
  show toReal (I.centerBoxMat.inf i j) ≤ I.nominal.center i j ∧
    I.nominal.center i j ≤ toReal (I.centerBoxMat.sup i j)
  rw [h]
  simp only [Interval.centerBoxMat, Interval.centerMat, toReal_half]
  have h1 := addDown_le_add (I.inf i j) (I.sup i j)
  have h2 := add_le_addUp (I.inf i j) (I.sup i j)
  constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

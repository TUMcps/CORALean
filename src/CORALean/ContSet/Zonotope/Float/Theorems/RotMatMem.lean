module

public import CORALean.ContSet.Zonotope.Float.Operations.RotMat
public import CORALean.ContSet.Zonotope.Real.Operations.RotMat

@[expose] public section

/-!
# The rotation lies in the interval `rotMat`

Entry by entry: the sine and cosine entries are within their enclosures, the others exact.

## Inputs
* `p` – Newton steps for the trigonometry
* `n` – dimension
* `i` – first rotation axis
* `j` – second rotation axis
* `angle` – rotation angle

## Hypotheses
* none

## Conclusion
* rotation lies in the interval matrix
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem rotMat_mem (p n : ℕ) (i j : Fin n) (angle : 𝕋) : -- --- CONCL ---
    Real.rotMat n i j (toReal angle) ∈ (rotMat p n i j angle).construct := by -- --- PROOF ---
  rintro ⟨a, b⟩
  have hc := And.intro (cosDown_le p angle) (le_cosUp p angle)
  have hs := And.intro (sinDown_le p angle) (le_sinUp p angle)
  have hz : toReal (zero : 𝕋) ≤ 0 ∧ (0 : ℝ) ≤ toReal (zero : 𝕋) := by rw [toReal_zero]; simp
  have ho : toReal (one : 𝕋) ≤ 1 ∧ (1 : ℝ) ≤ toReal (one : 𝕋) := by rw [toReal_one]; simp
  -- the same case split on both sides
  show toReal ((rotMat p n i j angle).inf a b) ≤ Real.rotMat n i j (toReal angle) a b ∧
    Real.rotMat n i j (toReal angle) a b ≤ toReal ((rotMat p n i j angle).sup a b)
  simp only [rotMat, Real.rotMat]
  split_ifs <;> first
    | exact hc | exact hs | exact hz | exact ho
    | (rw [toReal_neg, toReal_neg]; exact ⟨neg_le_neg hs.2, neg_le_neg hs.1⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

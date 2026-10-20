module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError

@[expose] public section

/-!
# The stored shifted centers of `absorbError` bracket the exact one

## Inputs
* `Z` – zonotope
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* shifted midpoint lies between the two rounded centers
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stored centers bracket the exact shifted one, which is what is left. -/
theorem Zonotope.shift_brackets_mid (Z : Zonotope (Vec 𝕋 n)) (i : Fin n) :
    let mid := toReal (Z.c i) + (toReal (Z.I_error.inf i) + toReal (Z.I_error.sup i)) / 2
    toReal (Z.shiftDown i) ≤ mid ∧ mid ≤ toReal (Z.shiftUp i) := by -- --- PROOF ---
  intro mid
  simp only [mid]
  constructor
  · have h1 := addDown_le_add (Z.c i) (half (addDown (Z.I_error.inf i) (Z.I_error.sup i)))
    have h2 := addDown_le_add (Z.I_error.inf i) (Z.I_error.sup i)
    rw [toReal_half] at h1
    simpa only [Zonotope.shiftDown] using by linarith
  · have h1 := add_le_addUp (Z.c i) (half (addUp (Z.I_error.inf i) (Z.I_error.sup i)))
    have h2 := add_le_addUp (Z.I_error.inf i) (Z.I_error.sup i)
    rw [toReal_half] at h1
    simpa only [Zonotope.shiftUp] using by linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

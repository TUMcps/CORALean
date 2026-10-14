module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError

@[expose] public section

/-!
# The new generators of `absorbError` reach every point the box did
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The new generators reach every point the box did. -/
theorem Zonotope.abs_sub_mid_le_errorRadius (Z : Zonotope (Vec 𝕋 n)) {e : Vec ℝ n}
    (he : e ∈ Z.I_error.construct) (i : Fin n) :
    |e i - (toReal (Z.I_error.inf i) + toReal (Z.I_error.sup i)) / 2|
      ≤ toReal (Z.errorRadius i) := by -- --- PROOF ---
  have hwidth := sub_le_subUp (Z.I_error.sup i) (Z.I_error.inf i)
  -- ascribed, so `toRealVec _ i` is unfolded to the atom linarith shares with hwidth
  have hlo : toReal (Z.I_error.inf i) ≤ e i := (he i).1
  have hhi : e i ≤ toReal (Z.I_error.sup i) := (he i).2
  simp only [Zonotope.errorRadius, toReal_half]
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

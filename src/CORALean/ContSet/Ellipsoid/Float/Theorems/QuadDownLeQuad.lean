module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `quadDown` bounds the quadratic form from below

Coordinate `i` of `Q a` lies between its two roundings, so `aᵢ (Q a)ᵢ`, linear in it, is at least
its value at the end of the bracket opposite `aᵢ`'s side, which the smaller of the two products
rounded down is below; the sum is rounded down.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `quadDown a ≤ aᵀ Q a`, `Q` and `a` the stored floats read as reals. -/
theorem Ellipsoid.quadDown_le_quad (E : Ellipsoid 𝕋 n) (a : Vec 𝕋 n) :
    toReal (E.quadDown a) ≤ toRealVec a ⬝ᵥ (toRealMat E.Q *ᵥ toRealVec a) := by -- --- PROOF ---
  refine le_trans (sumDown_le_sum _) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  -- `(Q a)ᵢ` between its roundings
  have hlo : toReal (mulVecDown E.Q a i) ≤ (toRealMat E.Q *ᵥ toRealVec a) i :=
    dotDown_le (E.Q i) a
  have hhi : (toRealMat E.Q *ᵥ toRealVec a) i ≤ toReal (mulVecUp E.Q a i) :=
    le_dotUp (E.Q i) a
  have h1 := mulDown_le_mul (a i) (mulVecDown E.Q a i)
  have h2 := mulDown_le_mul (a i) (mulVecUp E.Q a i)
  rw [toReal_minimum]
  show _ ≤ toReal (a i) * (toRealMat E.Q *ᵥ toRealVec a) i
  rcases le_total 0 (toReal (a i)) with ha | ha
  · exact le_trans (min_le_left _ _) (le_trans h1 (mul_le_mul_of_nonneg_left hlo ha))
  · exact le_trans (min_le_right _ _) (le_trans h2 (mul_le_mul_of_nonpos_left hhi ha))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

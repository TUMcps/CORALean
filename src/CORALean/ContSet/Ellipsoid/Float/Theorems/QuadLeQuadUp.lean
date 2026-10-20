module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `quadUp` bounds the quadratic form from above

Coordinate `i` of `Q a` lies between its two roundings, so `aᵢ (Q a)ᵢ`, linear in it, is at most
its value at the end of the bracket on `aᵢ`'s side, which the larger of the two products rounded
up covers; the sum is rounded up.

## Inputs
* `E` – ellipsoid
* `a` – vector

## Hypotheses
* none

## Conclusion
* `aᵀ Q a` is at most `quadUp a`
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

/-- `aᵀ Q a ≤ quadUp a`, `Q` and `a` the stored floats read as reals. -/
theorem Ellipsoid.quad_le_quadUp (E : Ellipsoid 𝕋 n) (a : Vec 𝕋 n) : -- --- CONCL ---
    toRealVec a ⬝ᵥ (toRealMat E.Q *ᵥ toRealVec a) ≤ toReal (E.quadUp a) := by -- --- PROOF ---
  refine le_trans ?_ (sum_le_sumUp _)
  refine Finset.sum_le_sum fun i _ => ?_
  -- `(Q a)ᵢ` between its roundings
  have hlo : toReal (mulVecDown E.Q a i) ≤ (toRealMat E.Q *ᵥ toRealVec a) i :=
    dotDown_le (E.Q i) a
  have hhi : (toRealMat E.Q *ᵥ toRealVec a) i ≤ toReal (mulVecUp E.Q a i) :=
    le_dotUp (E.Q i) a
  have h1 := mul_le_mulUp (a i) (mulVecDown E.Q a i)
  have h2 := mul_le_mulUp (a i) (mulVecUp E.Q a i)
  rw [toReal_maximum]
  show toReal (a i) * (toRealMat E.Q *ᵥ toRealVec a) i ≤ _
  rcases le_total 0 (toReal (a i)) with ha | ha
  · exact le_trans (mul_le_mul_of_nonneg_left hhi ha) (le_trans h2 (le_max_right _ _))
  · exact le_trans (mul_le_mul_of_nonpos_left hlo ha) (le_trans h1 (le_max_left _ _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

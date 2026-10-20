module

public import CORALean.ContSet.Conversion.Real.Definitions.GramSchmidt

@[expose] public section

/-!
# The first column of CORA's one-column `gramSchmidt(g)` is `g / ‖g‖₂`

Gram–Schmidt leaves its first vector alone but for the length (`gramSchmidt_bot`), and the
completion puts `g` first. At `g = 0` both sides are `0`.

## Inputs
* `g` – vector

## Hypotheses
* none

## Conclusion
* first column is the normalized vector
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The first column of CORA's `gramSchmidt(g)` is `g / ‖g‖₂`. -/
theorem gramSchmidtVec_col_zero (g : Vec ℝ (m + 1)) :
    (gramSchmidtVec g)ᵀ 0 = (‖g‖₂)⁻¹ • g := by -- --- PROOF ---
  funext i
  simp only [transpose_apply, gramSchmidtVec, gramSchmidt, InnerProductSpace.gramSchmidtNormed,
    Pi.smul_apply, smul_eq_mul]
  rw [show (0 : Fin (m + 1)) = ⊥ from rfl, InnerProductSpace.gramSchmidt_bot]
  show ‖toEuclidean g‖⁻¹ * toEuclidean g i = _
  rw [norm_toEuclidean, toEuclidean_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

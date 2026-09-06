import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

/-!
# Entrywise generator error, scaled by any coefficients in `[-1,1]`

No monomial is ever computed: what the float layer stores of a monomial is its
exponent column, over ℕ, so the monomial is an exact real, and this covers any
coefficient family — a zonotope's free one included.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Entrywise generator error scaled by any coefficients in `[-1,1]`. -/
theorem PolyZonotope.mem_generatorError {G : Mat 𝕋 n h} {Δ : Mat ℝ n h} {t : Vec ℝ h}
    (hG : ∀ i l, |Δ i l| ≤ toReal (G i l)) (ht : ∀ l, |t l| ≤ 1) :
    (fun i => ∑ l, Δ i l * t l) ∈ (PolyZonotope.generatorError G).construct := by -- --- PROOF ---
  intro i
  have key := abs_sum_le_radius (fun i l => le_trans (hG i l) (le_abs_self _)) ht i
  refine ⟨?_, le_of_abs_le key⟩
  show toReal (neg (radius G i)) ≤ ∑ l, Δ i l * t l
  rw [toReal_neg]
  exact neg_le_of_abs_le key

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

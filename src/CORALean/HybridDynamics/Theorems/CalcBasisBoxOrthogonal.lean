import CORALean.HybridDynamics.Operations.CalcBasisBox

/-!
# The `'box'` basis is orthogonal

A basis for an enclosure by rotated boxes must be invertible, and an orthogonal one is its own
inverse's transpose; the identity is orthogonal, so the enclosure is the interval hull itself.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `eye(n)` is `1`, so `B Bᵀ = Bᵀ B = 1`. -/
theorem Location.calcBasisBox_orthogonal (n : ℕ) :
    Location.calcBasisBox n * (Location.calcBasisBox n)ᵀ = 1 ∧
      (Location.calcBasisBox n)ᵀ * Location.calcBasisBox n = 1 := by -- --- PROOF ---
  have h : Location.calcBasisBox n = 1 := by
    funext i j
    simp [Location.calcBasisBox, Matrix.one_apply]
  rw [h]
  simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

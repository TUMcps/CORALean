module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.plusA`

Two constraint systems side by side, block-diagonally: each set's rows read
only its own constraint generators. The one place a matrix is still assembled
by hand — there is no polytope here to pull back along a projection the way
`ConZonotope.plus` does.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Two constraint systems side by side, block-diagonally: each set's rows read
only its own constraint generators. -/
def ConPolyZono.plusA {m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat ℝ m₁ q₁) (A₂ : Mat ℝ m₂ q₂) :
    Mat ℝ (m₁ + m₂) (q₁ + q₂) := fun i =>
  Fin.append (fun r => Fin.append (A₁ r) (0 : Fin q₂ → ℝ))
    (fun r => Fin.append (0 : Fin q₁ → ℝ) (A₂ r)) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.plusA`

Two constraint systems side by side, block-diagonally: each set's rows read
only its own constraint generators. The one place a matrix is still assembled
by hand — there is no polytope here to pull back along a projection the way
`ConZonotope.plus` does.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Two constraint systems side by side, block-diagonally: each set's rows read
only its own constraint generators. -/
def ConPolyZono.plusA {m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat ℝ m₁ s₁) (A₂ : Mat ℝ m₂ s₂) :
    Mat ℝ (m₁ + m₂) (s₁ + s₂) := fun i =>
  Fin.append (fun r => Fin.append (A₁ r) (0 : Fin s₂ → ℝ))
    (fun r => Fin.append (0 : Fin s₁ → ℝ) (A₂ r)) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

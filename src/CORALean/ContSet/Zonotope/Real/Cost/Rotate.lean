import CORALean.ContSet.Zonotope.Real.Operations.Rotate
import CORALean.ContSet.Zonotope.Real.Cost.Mtimes

/-!
# `Zonotope.rotateCost`

Asserted, not proved: `Operations/Rotate.lean` is `Zonotope.mtimes` at the plane
rotation `rotMat`, whose two nonzero entries cost a `cos` and a `sin`, priced
at one operation each, on top of `Zonotope.mtimesCost n n h`: the matrix is
applied dense, the zeros of the rotation not being exploited.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.rotate` costs at `Vec ℝ n` and `h` generators. -/
def Zonotope.rotateCost (n h : ℕ) : Cost := ⟨2⟩ + Zonotope.mtimesCost n n h

/-- Monotone in the generator count. -/
theorem Zonotope.rotateCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.rotateCost n h ≤ Zonotope.rotateCost n h' :=
  Cost.add_le_add (le_refl _) (Zonotope.mtimesCost_mono n n hh)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

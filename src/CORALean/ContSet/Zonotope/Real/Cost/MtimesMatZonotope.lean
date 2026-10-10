import CORALean.ContSet.Zonotope.Real.Operations.MtimesMatZonotope
import CORALean.ContSet.Zonotope.Real.Cost.Bilin

/-!
# `Zonotope.mtimesMatZonotopeCost`

Asserted, not proved: `Operations/MtimesMatZonotope.lean` is `Zonotope.bilin` at
matrix-vector application, one `Cost.matVec m n` per application.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.mtimesMatZonotope` costs at `M : Zonotope (Mat ℝ m n)` of `hM`
generators and `Z` of `h`. -/
def Zonotope.mtimesMatZonotopeCost (m n hM h : ℕ) : Cost :=
  Zonotope.bilinCost (Cost.matVec m n) hM h

/-- Monotone in both generator counts. -/
theorem Zonotope.mtimesMatZonotopeCost_mono {m n hM hM' h h' : ℕ} (a : hM ≤ hM') (b : h ≤ h') :
    Zonotope.mtimesMatZonotopeCost m n hM h ≤ Zonotope.mtimesMatZonotopeCost m n hM' h' :=
  Zonotope.bilinCost_mono _ a b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

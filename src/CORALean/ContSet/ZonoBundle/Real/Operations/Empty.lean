import CORALean.ContSet.ZonoBundle.Real.Operations.OfPoint
import Mathlib.Data.Fin.VecNotation

/-!
# `ZonoBundle.empty`

CORA's `zonoBundle.empty(n)` bundles one `n × 0` zonotope, which CORA reads as empty. A
`Zonotope` here always has a centre, so the empty bundle is two point-zonotopes with no point in
common, `0` and the first unit vector. That needs a coordinate: at `n = 0` the space has a
single point and no bundle of nonempty zonotopes is empty, so the definition takes `0 < n`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonoBundle.empty(n)` for `0 < n`: the bundle of the points `0` and `e₀`. -/
def ZonoBundle.empty (n : ℕ) (hn : 0 < n) : ZonoBundle (Vec ℝ n) :=
  ⟨2, ![Zonotope.ofPoint 0, Zonotope.ofPoint (Pi.single ⟨0, hn⟩ (1 : ℝ))]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Layers.Definitions.RegionPoly

@[expose] public section

/-!
# The region a relaxation is fitted on
A relaxation stores a polynomial and an error per box; on the box `[l, u]` its region is that
box with the polynomial and error stored for it, which is one entry of `findRegionPolys`'s result.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The relaxation's polynomial on the box `[l, u]` it is fitted on. -/
def RegionPoly.ofRelaxation {m : ℕ} (R : PolyRelaxation 𝕋 m) (l u : 𝕋) : RegionPoly 𝕋 :=
  ⟨some l, some u, m, R.coeffs l u, R.error l u⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

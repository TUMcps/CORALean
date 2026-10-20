module

public import CORALean.NN.Layers.Operations.FindRegionLoop

@[expose] public section

/-!
# `findRegionPolys`: polynomials with error at most a tolerance, covering the line
CORA's `nnActivationLayer/findRegionPolys`: the domain `[l_max, u_max]` is divided into
regions, each with a polynomial of order at most `order` and an error at most `tol`, the two
infinite ends carrying the given polynomials `pStart` and `pEnd`. The fit and its error bound are
the relaxation `F`, standing for `computeApproxPoly` with `'regression'` and
`computeApproxError`; the progress printing and the final sort by `l` are not modelled.

## Inputs
* `F` – polynomial relaxations by order
* `order` – polynomial order
* `tol` – error tolerance
* `fuel` – bound on the number of halvings
* `lMax` – left end of the domain
* `uMax` – right end of the domain
* `pStart` – polynomial left of the domain
* `pEnd` – polynomial right of the domain

## Output
* start region, the regions found and the end region, or none if not converged
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Start region, the regions found, end region; `none` is `CORA:notConverged`. -/
def findRegionPolys (F : (o : ℕ) → PolyRelaxation 𝕋 o) (order : ℕ) (tol : 𝕋) (fuel : ℕ)
    (lMax uMax : 𝕋) (pStart pEnd : RegionPoly 𝕋) : Option (List (RegionPoly 𝕋)) :=
  (findRegionLoop F order tol fuel lMax uMax []).map fun mids => pStart :: (mids ++ [pEnd])

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

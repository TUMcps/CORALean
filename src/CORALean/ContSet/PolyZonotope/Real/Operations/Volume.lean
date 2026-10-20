module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# `PolyZonotope.volume`

CORA's `@polyZonotope/volume_`: the independent generators become dependent ones
(`dependent`), and then, with exactly as many factors as dimensions, the integral of the
Jacobian determinant over the factor cube `[-1,1]ᵖ`. With fewer factors than dimensions the
volume is `0`; with more CORA throws `CORA:notSupported`, which is `none`. The integrand is the
*signed* determinant, the volume of the image only where the map is injective and the
determinant does not change sign; CORA's comment claims more (see `volume_neg_example`).

## Inputs
* `pZ` – polynomial zonotope

## Output
* volume of the set, if the factor count permits
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}
open MeasureTheory


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

noncomputable def PolyZonotope.aux_jacobianDetIntegral (pZ : PolyZonotope (Vec ℝ n))
    (h : pZ.p = n) : ℝ :=
  ∫ a in Set.Icc (fun _ : Fin pZ.p => (-1 : ℝ)) (fun _ => 1),
    (Matrix.of fun (i k : Fin n) => pZ.jacobianMat a i (Fin.cast h.symm k) : Mat ℝ n n).det


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `polyZonotope/volume_`; `none` where CORA throws (more factors than dimensions). -/
noncomputable def PolyZonotope.volume (pZ : PolyZonotope (Vec ℝ n)) : Option ℝ :=
  -- redefine independent generators as new dependent generators
  let pZ' := if pZ.q = 0 then pZ else pZ.dependent
  if pZ'.p < n then some 0
  else if h : pZ'.p = n then some (pZ'.aux_jacobianDetIntegral h)
  else none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

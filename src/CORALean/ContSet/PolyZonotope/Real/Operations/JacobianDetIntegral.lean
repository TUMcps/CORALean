module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# `PolyZonotope.jacobianDetIntegral`

The integral of the Jacobian determinant over the factor cube `[-1,1]ᵖ`, at `p = n` factors:
what CORA's `@polyZonotope/volume_` computes symbolically, factor by factor. The integrand is
the *signed* determinant.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.jacobianDetIntegral (pZ : PolyZonotope (Vec ℝ n))
    (h : pZ.p = n) : ℝ :=
  ∫ a in Set.Icc (fun _ : Fin pZ.p => (-1 : ℝ)) (fun _ => 1),
    (Matrix.of fun (i k : Fin n) => pZ.jacobianMat a i (Fin.cast h.symm k) : Mat ℝ n n).det

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

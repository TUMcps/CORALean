module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Volume
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AreaFormula
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ConstructOfQZero
public import CORALean.ContSet.PolyZonotope.Real.Theorems.HasFDerivAtPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.Basic

@[expose] public section

/-!
# Where the signed integral is the volume: the bound

CORA's `volume_` integrates `det J`, not `|det J|`. Where `det J ≥ 0` on the factor cube the
two agree, and the area formula bounds the volume of the image by CORA's value. Nothing is
claimed where the determinant changes sign, and `volume_neg_example` shows the value is not a
volume there.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* `hq` – no independent generators
* `h` – factor count equals the dimension
* `hdet` – determinant is nonnegative on the cube

## Conclusion
* volume of the set is at most the integral of the determinant
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `det J ≥ 0` on the factor cube the volume of the set is at most CORA's value. -/
theorem PolyZonotope.volume_le_of_det_nonneg (pZ : PolyZonotope (Vec ℝ n)) (hq : pZ.q = 0)
    (h : pZ.p = n)
    (hdet : ∀ a ∈ Set.Icc (fun _ : Fin pZ.p => (-1 : ℝ)) (fun _ => 1),
      0 ≤ (Matrix.of fun (i k : Fin n) => pZ.jacobianMat a i (Fin.cast h.symm k)
        : Mat ℝ n n).det) : -- --- CONCL ---
    MeasureTheory.volume pZ.construct
      ≤ ENNReal.ofReal (pZ.aux_jacobianDetIntegral h) := by -- --- PROOF ---
  -- destructure, so that `p = n` and `q = 0` can be substituted
  obtain ⟨p, hh, q, c, G, E, GI⟩ := pZ
  change q = 0 at hq
  change p = n at h
  subst hq
  subst h
  rw [PolyZonotope.construct_of_q_zero _ rfl]
  simp only [Fin.cast_eq_self] at hdet
  exact (PolyZonotope.area_formula (PolyZonotope.point (PolyZonotope.mk p hh 0 c G E GI))
    (PolyZonotope.jacobianMat (PolyZonotope.mk p hh 0 c G E GI))
    (fun a => PolyZonotope.hasFDerivAt_point _ a)
    (continuous_pi fun i => continuous_pi fun k =>
      (continuous_apply i).comp (PolyZonotope.continuous_point
        (PolyZonotope.jacobian (PolyZonotope.mk p hh 0 c G E GI) k))) hdet).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

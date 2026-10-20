module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Volume
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AreaFormula
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ConstructOfQZero
public import CORALean.ContSet.PolyZonotope.Real.Theorems.HasFDerivAtPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.Basic

@[expose] public section

/-!
# Where the signed integral is the volume: equality

With `det J ≥ 0` on the factor cube and the factor map injective on it, CORA's value is the
volume of the set, the area formula's equality case.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* `hq` – no independent generators
* `h` – factor count equals the dimension
* `hdet` – determinant is nonnegative on the cube
* `hinj` – the point map is injective on the cube

## Conclusion
* volume of the set equals the integral of the determinant
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

/-- With the factor map injective on the cube as well, CORA's value is the volume. -/
theorem PolyZonotope.volume_eq_of_det_nonneg_injOn (pZ : PolyZonotope (Vec ℝ n))
    (hq : pZ.q = 0) (h : pZ.p = n)
    (hdet : ∀ a ∈ Set.Icc (fun _ : Fin pZ.p => (-1 : ℝ)) (fun _ => 1),
      0 ≤ (Matrix.of fun (i k : Fin n) => pZ.jacobianMat a i (Fin.cast h.symm k)
        : Mat ℝ n n).det)
    (hinj : Set.InjOn pZ.point (Set.Icc (fun _ : Fin pZ.p => (-1 : ℝ)) (fun _ => 1)))
    : -- --- CONCL ---
    MeasureTheory.volume pZ.construct
      = ENNReal.ofReal (pZ.aux_jacobianDetIntegral h) := by -- --- PROOF ---
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
        (PolyZonotope.jacobian (PolyZonotope.mk p hh 0 c G E GI) k))) hdet).2 hinj

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

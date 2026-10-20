module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Project
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
public import CORALean.ContSet.Interval.Float.Theorems.ProjectOuter
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MapSelection
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `Ellipsoid.project` over-approximates the projection

Selecting coordinates is linear and rounds nothing, so `InflatedContSet.image_subset` splits
this into the nominal ellipsoid and the box. At a positive semi-definite `Q` the projection's
nominal ellipsoid is the exact layer's `project`, `Q(dims, dims)` (`aux_nominal_project`), and
`project_exact` gives the nominal obligation as an equality; where `Q` is refused the nominal
part is its center, whose projection is the projection's center. The box is
`Interval.project_outer`.

## Inputs
* `E` – ellipsoid
* `dims` – kept coordinates

## Hypotheses
* none

## Conclusion
* the projection of `E` lies in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- At a positive semi-definite `Q` the projection's nominal ellipsoid is the exact projection. -/
theorem Ellipsoid.aux_nominal_project (E : Ellipsoid 𝕋 n) (dims : Fin m → Fin n)
    (h : (toRealMat E.Q).PosSemidef) : -- --- CONCL ---
    (nominal (E.project dims)).ellipsoid = Real.Ellipsoid.project (nominal E).ellipsoid dims
    := by -- --- PROOF ---
  have hsel :=
    (nominal E).ellipsoid.map_selection dims (LinearMap.funLeft ℝ ℝ dims) (fun _ _ => rfl)
  have h' : (toRealMat (E.project dims).Q).PosSemidef := h.submatrix dims
  refine Real.Ellipsoid.ext ?_ ?_
  · show _ = (Real.Ellipsoid.map _ _).Q
    rw [hsel.1, Ellipsoid.nominal_of_psd h', Ellipsoid.nominal_of_psd h]
    rfl
  · show _ = (Real.Ellipsoid.map _ _).q
    rw [hsel.2, Ellipsoid.nominal_q, Ellipsoid.nominal_q]
    rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.project_outer (E : Ellipsoid 𝕋 n) (dims : Fin m → Fin n) : -- --- CONCL ---
    (fun x k => x (dims k)) '' E.construct ⊆ (E.project dims).construct := by -- --- PROOF ---
  refine image_subset (fun _ _ => rfl) ?_ (Interval.project_outer E.I_error dims)
  by_cases h : (toRealMat E.Q).PosSemidef
  · -- the exact projection, at a positive semi-definite `Q`
    have he := Real.Ellipsoid.project_exact (nominal E).ellipsoid dims
    rw [← Ellipsoid.aux_nominal_project E dims h] at he
    exact le_of_eq he
  · -- a refused `Q`: the center alone, whose projection is the projection's center
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, -, rfl⟩ := Ellipsoid.mem_nominalSet_iff.mp hx
    have hG : (nominal E).ellipsoid.G = 0 := by
      rw [Real.Ellipsoid.G_eq_zero_iff, Ellipsoid.nominal_Q_eq, if_neg h]
    rw [hG, Matrix.zero_mulVec, add_zero]
    exact Ellipsoid.mem_nominalSet_iff.mpr ⟨0, by rw [norm₂_zero]; exact zero_le_one,
      by rw [Matrix.mulVec_zero, add_zero]; rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

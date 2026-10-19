module

public import CORALean.ContSet.InflatedContSet.Theorems.ImageAdd
public import CORALean.ContSet.Interval.Float.Theorems.ReindexExact
public import CORALean.ContSet.Ellipsoid.Float.Operations.Reindex
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MapExact
public import CORALean.ContSet.Ellipsoid.Real.Instances
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MapSelection
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic

@[expose] public section

/-!
# `Ellipsoid.reindex` is exactly the relabelled set, in float too

An equality, in the layer where every other guarantee is an enclosure, because a
relabelling does no arithmetic. The nominal part is the exact layer's `map` at
the relabelling, `Q` at the relabelled rows and columns (`Real.Ellipsoid.map_selection`), and
positive semi-definite exactly when the stored one is; the box
is relabelled alongside, and a linear map distributes over the sum.

## Inputs
* `e` – equivalence of the coordinates
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* the result is exactly the relabelled set
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The relabelled nominal ellipsoid is the exact layer's `map` at the relabelling. -/
theorem aux_reindex_nominal (e : Fin m ≃ Fin n) (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal (E.reindex e)).ellipsoid
      = Real.Ellipsoid.map (reindexLin e) (InflatedContSet.nominal E).ellipsoid
    := by -- --- PROOF ---
  have hsel :=
    (InflatedContSet.nominal E).ellipsoid.map_selection e (reindexLin e) (fun _ _ => rfl)
  -- relabelling preserves positive semi-definiteness both ways
  have hiff : (toRealMat (E.reindex e).Q).PosSemidef ↔ (toRealMat E.Q).PosSemidef :=
    Matrix.posSemidef_submatrix_equiv (M := toRealMat E.Q) e
  refine Real.Ellipsoid.ext ?_ ?_
  · rw [hsel.1, Ellipsoid.nominal_Q_eq, Ellipsoid.nominal_Q_eq]
    by_cases h : (toRealMat E.Q).PosSemidef
    · rw [if_pos (hiff.2 h), if_pos h]
      rfl
    · rw [if_neg (mt hiff.1 h), if_neg h]
      rfl
  · rw [hsel.2, Ellipsoid.nominal_q, Ellipsoid.nominal_q]
    rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.reindex_exact (e : Fin m ≃ Fin n) (E : Ellipsoid 𝕋 n) :
    (E.reindex e).construct = reindexLin e '' E.construct := by -- --- PROOF ---
  show InflatedContSet.nominalSet (E.reindex e) + (E.I_error.reindex e).construct
    = reindexLin e '' (InflatedContSet.nominalSet E + E.I_error.construct)
  have h : InflatedContSet.nominalSet (E.reindex e)
      = reindexLin e '' InflatedContSet.nominalSet E := by
    show (InflatedContSet.nominal (E.reindex e)).ellipsoid.construct
      = reindexLin e '' (InflatedContSet.nominal E).ellipsoid.construct
    rw [aux_reindex_nominal]
    exact (Real.Ellipsoid.map_exact (reindexLin e) (InflatedContSet.nominal E).ellipsoid).symm
  rw [InflatedContSet.image_add, Interval.reindex_exact e E.I_error, h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

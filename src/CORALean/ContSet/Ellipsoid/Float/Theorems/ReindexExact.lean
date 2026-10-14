module

public import CORALean.ContSet.InflatedContSet.Theorems.ImageAdd
public import CORALean.ContSet.Interval.Float.Theorems.ReindexExact
public import CORALean.ContSet.Ellipsoid.Float.Operations.Reindex
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MapExact
public import CORALean.ContSet.Ellipsoid.Real.Instances

@[expose] public section

/-!
# `Ellipsoid.reindex` is exactly the relabelled set, in float too

An equality, in the layer where every other guarantee is an enclosure, because a
relabelling does no arithmetic. The nominal part is the exact layer's `map` at
the relabelling, the matrix `toMatrix' (reindexLin e)` selecting rows; the box
is relabelled alongside, and a linear map distributes over the sum.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The relabelled nominal ellipsoid is the exact layer's `map` at the relabelling. -/
theorem aux_reindex_nominal (e : Fin m ≃ Fin n) (E : Ellipsoid 𝕋 n) :
    InflatedContSet.nominal (E.reindex e)
      = Real.Ellipsoid.map (reindexLin e) (InflatedContSet.nominal E) := by -- --- PROOF ---
  unfold Real.Ellipsoid.map
  show (⟨E.k, toRealVec fun i => E.q (e i), toRealMat fun i j => E.G (e i) j⟩ : Real.Ellipsoid m)
    = ⟨E.k, LinearMap.toMatrix' (reindexLin e) *ᵥ toRealVec E.q,
        LinearMap.toMatrix' (reindexLin e) * toRealMat E.G⟩
  congr 1
  · rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  · funext i j
    rw [Matrix.mul_apply]
    simp [LinearMap.toMatrix'_apply, reindexLin, toRealMat, Pi.single_apply]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.reindex_exact (e : Fin m ≃ Fin n) (E : Ellipsoid 𝕋 n) :
    (E.reindex e).construct = reindexLin e '' E.construct := by -- --- PROOF ---
  show InflatedContSet.nominalSet (E.reindex e) + (E.I_error.reindex e).construct
    = reindexLin e '' (InflatedContSet.nominalSet E + E.I_error.construct)
  have h : InflatedContSet.nominalSet (E.reindex e)
      = reindexLin e '' InflatedContSet.nominalSet E := by
    unfold InflatedContSet.nominalSet
    rw [aux_reindex_nominal]
    exact (Real.Ellipsoid.map_exact (reindexLin e) (InflatedContSet.nominal E)).symm
  rw [InflatedContSet.image_add, Interval.reindex_exact e E.I_error, h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

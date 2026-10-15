module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Mtimes
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AddSubMemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.InflateSubPosSemidef
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MtimesExact
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.InflatedContSet.Theorems.MapSubset

@[expose] public section

/-!
# `Ellipsoid.mtimes` over-approximates the image under a linear map

`InflatedContSet.map_subset` splits this into the nominal part and the box. The image of the
nominal ellipsoid is exactly `Real.Ellipsoid.mtimes` (`M Q Mᵀ`, `M q`), and the stored shape
dominates `M Q Mᵀ` (`inflate_sub_posSemidef`, `M Q Mᵀ` lying in the interval matrix and symmetric
with `Q`), so the image about the stored center lies in the nominal part
(`add_sub_mem_nominalSet`). Where `Q` is refused the nominal part is a point and so is its
image. What is left is the center's rounding, which `mtimesResidual` holds.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The image's nominal part, with the center's rounding charged to a box. -/
theorem Ellipsoid.aux_mtimes_nominal (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) :
    (toRealMat M *ᵥ ·) '' nominalSet E ⊆
      nominalSet (Ellipsoid.mtimes M E)
        + (Ellipsoid.mtimesResidual M E).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  set Mr : Mat ℝ m n := toRealMat M with hMr
  set F : Real.Ellipsoid m := Real.Ellipsoid.mtimes Mr (nominal E).ellipsoid with hFdef
  have hxF : Mr *ᵥ x ∈ F.construct := by
    rw [hFdef, ← Real.Ellipsoid.mtimes_exact]
    exact ⟨x, hx, rfl⟩
  -- the stored shape dominates `M Q Mᵀ`, or the nominal part is a point
  have hF : F.Q = 0 ∨ (toRealMat (Ellipsoid.mtimes M E).Q - F.Q).PosSemidef := by
    show Mr * (nominal E).ellipsoid.Q * Mrᵀ = 0
      ∨ (toRealMat (Ellipsoid.mtimes M E).Q - Mr * (nominal E).ellipsoid.Q * Mrᵀ).PosSemidef
    rw [Ellipsoid.nominal_Q_eq]
    split_ifs with h
    · refine Or.inr (Ellipsoid.inflate_sub_posSemidef (Interval.mem_mat_iff.mp ?_) ?_)
      · exact Interval.matMul_outer _ _ (Interval.matMul_outer _ _ (Interval.mem_point M)
          (Interval.mem_point E.Q)) (Interval.mem_point Mᵀ)
      · intro i j
        have hQt : (toRealMat E.Q)ᵀ = toRealMat E.Q := by
          simpa [conjTranspose_eq_transpose_of_trivial] using h.isHermitian.eq
        have ht : (Mr * toRealMat E.Q * Mrᵀ)ᵀ = Mr * toRealMat E.Q * Mrᵀ := by
          rw [transpose_mul, transpose_mul, transpose_transpose, hQt, Matrix.mul_assoc]
        exact (congrFun (congrFun ht j) i)
    · exact Or.inl (by rw [Matrix.mul_zero, Matrix.zero_mul])
  have hmem := Ellipsoid.add_sub_mem_nominalSet hF hxF
  -- the center's rounding
  have hq : F.q = Mr *ᵥ toRealVec E.q := by
    show Mr *ᵥ (nominal E).ellipsoid.q = _
    rw [Ellipsoid.nominal_q]
  refine ⟨_, hmem, fun i => (Mr *ᵥ toRealVec E.q) i - toReal (mulVecDown M E.q i),
    Interval.sub_mem_residual fun i => ⟨dotDown_le (M i) E.q, le_dotUp (M i) E.q⟩, ?_⟩
  funext i
  rw [hq]
  simp only [Pi.add_apply, Pi.sub_apply, toRealVec]
  show toReal (mulVecDown M E.q i) + _ + _ = _
  ring

/-- The old box travels through the map as a box, and the spill is added on. -/
theorem Ellipsoid.aux_mtimes_error (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) :
    (toRealMat M *ᵥ ·) '' (I_error E).construct + (Ellipsoid.mtimesResidual M E).construct ⊆
      (I_error (Ellipsoid.mtimes M E)).construct :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M E.I_error))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.mtimes_outer (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) :
    (toRealMat M *ᵥ ·) '' E.construct ⊆ (Ellipsoid.mtimes M E).construct :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (Ellipsoid.aux_mtimes_nominal M E) (Ellipsoid.aux_mtimes_error M E)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

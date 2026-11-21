module

public import CORALean.ContSet.Ellipsoid.Float.Operations.MtimesCora
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
# `Ellipsoid.mtimesCora` over-approximates the image under a linear map

`InflatedContSet.map_subset` splits this into the nominal part and the box. The image of the
nominal ellipsoid is exactly `Real.Ellipsoid.mtimes` (`M Q Mᵀ`, `M q`), and the stored shape
dominates `M Q Mᵀ` (`inflate_sub_posSemidef`, `M Q Mᵀ` lying in the symmetrized interval matrix
(`aux_symmCora_outer`) and symmetric with `Q`), so the image about the stored center lies in the
nominal part
(`add_sub_mem_nominalSet`). Where `Q` is refused the nominal part is a point and so is its
image. What is left is the center's rounding, which `mtimesResidual` holds.

## Inputs
* `M` – matrix
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* the image of `E` under `M` lies in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       21-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A symmetric matrix of `X` lies in its symmetrization, whose ends bracket both mirrored
entries. -/
private theorem Ellipsoid.aux_symmCora_outer {X : Interval (Mat 𝕋 n n)} {S : Mat ℝ n n}
    (hS : S ∈ X.toSet) (hT : ∀ i j, S j i = S i j) : -- --- CONCL ---
    S ∈ X.symmCora.toSet := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have h1 := Interval.mem_mat_iff.mp hS i j
  have h2 := Interval.mem_mat_iff.mp hS j i
  have e := hT i j
  have a1 := addDown_le_add (X.inf i j) (X.inf j i)
  have a2 := add_le_addUp (X.sup i j) (X.sup j i)
  show toReal (half (addDown (X.inf i j) (X.inf j i))) ≤ S i j ∧
    S i j ≤ toReal (half (addUp (X.sup i j) (X.sup j i)))
  rw [toReal_half, toReal_half]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The image's nominal part, with the center's rounding charged to a box. -/
private theorem Ellipsoid.aux_mtimesCora_nominal (M : Mat 𝕋 m n)
    (E : Ellipsoid 𝕋 n) : -- --- CONCL ---
    (toRealMat M *ᵥ ·) '' nominalSet E ⊆
      nominalSet (Ellipsoid.mtimesCora M E)
        + (Ellipsoid.mtimesResidual M E).toSet := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  set Mr : Mat ℝ m n := toRealMat M with hMr
  set F : Real.Ellipsoid m := Real.Ellipsoid.mtimes Mr (nominal E).ellipsoid with hFdef
  have hxF : Mr *ᵥ x ∈ F.toSet := by
    rw [hFdef, ← Real.Ellipsoid.mtimes_exact]
    exact ⟨x, hx, rfl⟩
  -- the stored shape dominates `M Q Mᵀ`, or the nominal part is a point
  have hF : F.Q = 0 ∨ (toRealMat (Ellipsoid.mtimesCora M E).Q - F.Q).PosSemidef := by
    show Mr * (nominal E).ellipsoid.Q * Mrᵀ = 0
      ∨ (toRealMat (Ellipsoid.mtimesCora M E).Q - Mr * (nominal E).ellipsoid.Q * Mrᵀ).PosSemidef
    rw [Ellipsoid.nominal_Q_eq]
    split_ifs with h
    · have hQt : (toRealMat E.Q)ᵀ = toRealMat E.Q := by
        simpa [conjTranspose_eq_transpose_of_trivial] using h.isHermitian.eq
      have ht : (Mr * toRealMat E.Q * Mrᵀ)ᵀ = Mr * toRealMat E.Q * Mrᵀ := by
        rw [transpose_mul, transpose_mul, transpose_transpose, hQt, Matrix.mul_assoc]
      refine Or.inr (Ellipsoid.inflate_sub_posSemidef (Interval.mem_mat_iff.mp ?_) ?_)
      · refine Ellipsoid.aux_symmCora_outer ?_ fun i j => congrFun (congrFun ht i) j
        exact Interval.matMul_outer _ _ (Interval.matMul_outer _ _ (Interval.mem_point M)
          (Interval.mem_point E.Q)) (Interval.mem_point Mᵀ)
      · intro i j
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
private theorem Ellipsoid.aux_mtimesCora_error (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) :
    (toRealMat M *ᵥ ·) '' (I_error E).toSet + (Ellipsoid.mtimesResidual M E).toSet ⊆
      (I_error (Ellipsoid.mtimesCora M E)).toSet :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M E.I_error))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.mtimesCora_outer (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) :
    (toRealMat M *ᵥ ·) '' E.toSet ⊆ (Ellipsoid.mtimesCora M E).toSet :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (Ellipsoid.aux_mtimesCora_nominal M E) (Ellipsoid.aux_mtimesCora_error M E)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

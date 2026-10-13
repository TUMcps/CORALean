module

public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsResidualLe
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MulVecSplit
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

@[expose] public section

/-!
# `Zonotope.mtimesIntervalMat` over-approximates every matrix in the box

A member `A` of the box acts on `z + e`, `z` in the nominal zonotope and `e` in
the error box, as `mid(M)(z + e) + (A - mid(M)) z + (A - mid(M)) e`. `mtimes_outer`
covers the first; the third is the box-times-box product
`Interval.mtimesIntervalMat_outer` encloses; the second is at most
`|A - mid(M)| (|c| + Σ|G|)` per coordinate, which is the rounded-up radius of
the new diagonal generators, so a coefficient in `[-1, 1]` reaches it
(`Real.Zonotope.coefficient`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   25-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimesIntervalMat_outer (IM : Interval (Mat 𝕋 m n)) (Z : Zonotope (Vec 𝕋 n)) :
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' Z.construct) ⊆
      (Zonotope.mtimesIntervalMat IM Z).construct := by -- --- PROOF ---
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, x, hxmem, rfl⟩ := hy
  obtain ⟨z, hz, e, he, rfl⟩ := hxmem
  set C := Interval.centreMat IM
  set Rs := Interval.matResidual IM.inf IM.sup C
  set R : Mat ℝ m n := fun i j => A i j - toReal (C i j)
  -- the centre matrix acts through `mtimes`, already proven sound
  obtain ⟨t₀, ht₀, e₀, he₀, hsum⟩ := Zonotope.mtimes_outer C Z ⟨z + e, ⟨z, hz, e, he, rfl⟩, rfl⟩
  have hsum' : t₀ + e₀ = toRealMat C *ᵥ (z + e) := hsum
  -- `A` known only to within `matResidual` of the centre matrix
  have hR : R ∈ Rs.construct := Interval.sub_mem_matResidual fun i j => hA (i, j)
  -- the residual on the error box, box times box
  have hRe : R *ᵥ e ∈ (Interval.mtimesIntervalMat Rs Z.E).construct :=
    Interval.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hR ⟨e, he, rfl⟩)
  -- the residual on the nominal part, within the new generators
  have hbound := Zonotope.abs_residual_le IM hR hz
  obtain ⟨γ, hγ, ht₀γ⟩ := Zonotope.mem_nominalSet_iff.mp ht₀
  set b : Vec 𝕋 m := fun i => sumUp fun j =>
    mulUp (maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j)))
      (addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j))
  have hb0 : ∀ i, 0 ≤ toReal (b i) := fun i => le_trans (abs_nonneg _) (hbound i)
  refine ⟨t₀ + R *ᵥ z, ?_, e₀ + R *ᵥ e, Interval.plus_outer _ _ (Set.add_mem_add he₀ hRe), ?_⟩
  · -- the witness: `mid(M) Z`'s coefficients, then one per coordinate scaled to the radius
    refine Zonotope.mem_nominalSet_iff.mpr
      ⟨Fin.append γ (fun i => Real.Zonotope.coefficient (toReal (b i)) ((R *ᵥ z) i)), ?_,
        fun i => ?_⟩
    · refine Fin.addCases (fun l => ?_) (fun i => ?_)
      · simpa using hγ l
      · simp only [Fin.append_right]
        exact Real.Zonotope.abs_coefficient_le_one (hb0 i) (hbound i)
    · show t₀ i + (R *ᵥ z) i = toReal (mulVecDown C Z.c i)
        + ∑ j : Fin (Z.h + m), toReal (Fin.append (fun l => mulVecDown C (Z.G l))
          (diagonalBlock b) j i) * Fin.append (m := Z.h) γ
            (fun i => Real.Zonotope.coefficient (toReal (b i)) ((R *ᵥ z) i)) j
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, toReal_diagonalBlock]
      rw [Real.Zonotope.sum_diagonal_mul', toRealVec, Real.Zonotope.mul_coefficient (hbound i),
        ht₀γ i, add_assoc]
      rfl
  · show t₀ + R *ᵥ z + (e₀ + R *ᵥ e) = A *ᵥ (z + e)
    rw [Zonotope.mulVec_split IM A (z + e), ← hsum', Matrix.mulVec_add]
    abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

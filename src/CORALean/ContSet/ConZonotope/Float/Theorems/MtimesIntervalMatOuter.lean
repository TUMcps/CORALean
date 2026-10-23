module

public import CORALean.ContSet.ConZonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.ConZonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemPadLeftNominalIff
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsResidualLe
public import CORALean.ContSet.Zonotope.Float.Theorems.MulVecSplit
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `ConZonotope.mtimesIntervalMat` over-approximates every image

`Zonotope.mtimesIntervalMat_outer`'s argument with the constraints along. A point `x = z + e`
of the set has coefficients `β` of the constraints; the center matrix `mid(M)` maps it through
`ConZonotope.mtimes_outer`, which keeps `β`, and what any `A` of the interval matrix does
beyond `mid(M)` is `R = A - mid(M)`, a matrix in `matResidual`. On the nominal part `R z` is
within the new generators' radius, so one new coefficient per coordinate absorbs it, and those
coefficients meet no constraint; on the error box `R e` is in the box-times-box product.

## Inputs
* `IM` – interval matrix
* `cZ` – float constrained zonotope

## Hypotheses
* none

## Conclusion
* every image under a matrix of the interval is contained in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of a constrained zonotope's nominal part is one of its unconstrained zonotope's. -/
theorem ConZonotope.aux_nominal_zonotope {cZ : ConZonotope 𝕋 (Vec 𝕋 n)} {z : Vec ℝ n}
    (hz : z ∈ nominalSet cZ) : z ∈ nominalSet cZ.zonotope := by
  obtain ⟨β, hβ, -, hzβ⟩ := ConZonotope.mem_nominalSet_iff.mp hz
  exact Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, hzβ⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mtimesIntervalMat_outer (IM : Interval (Mat 𝕋 m n))
    (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' cZ.construct) ⊆
      (ConZonotope.mtimesIntervalMat IM cZ).construct := by -- --- PROOF ---
  -- a point of the set, split into its nominal part and its error
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, x, hxmem, rfl⟩ := hy
  obtain ⟨z, hz, e, he, rfl⟩ := hxmem
  set C := Interval.centerMat IM
  set Rs := Interval.matResidual IM.inf IM.sup C
  set R : Mat ℝ m n := fun i j => A i j - toReal (C i j)
  -- the center matrix acts through `mtimes`, already proven sound
  obtain ⟨t₀, ht₀, e₀, he₀, hsum⟩ :=
    ConZonotope.mtimes_outer C cZ ⟨z + e, ⟨z, hz, e, he, rfl⟩, rfl⟩
  have hsum' : t₀ + e₀ = toRealMat C *ᵥ (z + e) := hsum
  -- `A` known only to within `matResidual` of the center matrix
  have hR : R ∈ Rs.construct := Interval.sub_mem_matResidual fun i j => hA (i, j)
  -- the residual on the error box, box times box
  have hRe : R *ᵥ e ∈ (Interval.mtimesIntervalMat Rs cZ.I_error).construct :=
    Interval.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hR ⟨e, he, rfl⟩)
  -- the residual on the nominal part, within the new generators
  have hbound' := Zonotope.abs_residual_le IM hR (ConZonotope.aux_nominal_zonotope hz)
  obtain ⟨γ₀, hγ₀, hPγ₀, ht₀γ₀⟩ := ConZonotope.mem_nominalSet_iff.mp ht₀
  -- the product's coefficient count is `cZ.h`, definitionally
  let γ : Vec ℝ cZ.h := γ₀
  have hγ : ∀ j, |γ j| ≤ 1 := hγ₀
  have hPγ : γ ∈ (ConZonotope.mtimes C cZ).P.nominal.construct := hPγ₀
  have ht₀γ : ∀ i, t₀ i = toReal ((ConZonotope.mtimes C cZ).c i)
      + ∑ j, toReal ((ConZonotope.mtimes C cZ).G j i) * γ j := ht₀γ₀
  set b : Vec 𝕋 m := fun i => sumUp fun j =>
    mulUp (maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j)))
      (addUp (absolute (cZ.c j)) (radius (fun i j => cZ.G j i) j)) with hb
  have hbound : ∀ i, |(R *ᵥ z) i| ≤ toReal (b i) := hbound'
  -- the new coefficients stay in `[-1, 1]`, and the sum of the new point is the image
  have hb0 : ∀ i, 0 ≤ toReal (b i) := fun i => le_trans (abs_nonneg _) (hbound i)
  refine ⟨t₀ + R *ᵥ z, ?_, e₀ + R *ᵥ e, Interval.plus_outer _ _ (Set.add_mem_add he₀ hRe), ?_⟩
  · -- the witness: `mid(M) cZ`'s coefficients, then one per coordinate scaled to the radius
    refine ConZonotope.mem_nominalSet_iff.mpr
      ⟨Fin.append γ (fun i => Real.Zonotope.coefficient (toReal (b i)) ((R *ᵥ z) i)), ?_, ?_,
        fun i => ?_⟩
    · -- the old coefficients are `γ`, the new ones are scaled to at most one
      refine Fin.addCases (fun l => ?_) (fun i => ?_)
      · simpa using hγ l
      · simp only [Fin.append_right]
        exact Real.Zonotope.abs_coefficient_le_one (hb0 i) (hbound i)
    · -- the constraints only see the old coefficients
      refine HPolytope.mem_padLeft_nominal_iff.mpr ?_
      show blockLeft cZ.h m (Fin.append γ _) ∈ _
      rw [blockLeft_append]
      exact hPγ
    · -- the stored center and generators recombine into the image
      show t₀ i + (R *ᵥ z) i = toReal (mulVecDown C cZ.c i)
        + ∑ j : Fin (cZ.h + m), toReal (Fin.append (fun j => mulVecDown C (cZ.G j))
          (diagonalBlock b) j i) * Fin.append (m := cZ.h) γ
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

module

public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemMatIff
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.Zonotope.Float.Operations.IntersectStrip
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

@[expose] public section

/-!
# `Zonotope.intersectStrip` over a float scalar encloses the intersection with the strips

Whatever the stored weights, the point `x` is `(I - Λ C) x + Λ (C x)`, with `(I - Λ C)` a member
of the interval matrix `Zonotope.mtimesIntervalMat` takes and `C x` a point of the box-shaped
strip zonotope, `y + φ ⊙ γ` with `γ ∈ [-1, 1]^p`. The strips are read as real numbers
`|C x - y| ≤ φ` at the stored values.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.intersectStrip_outer (C : Mat 𝕋 p n) (φ y : Vec 𝕋 p) (Λ : Mat 𝕋 n p)
    (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ∩ {x | ∀ i, |(toRealMat C *ᵥ x - toRealVec y) i| ≤ toReal (φ i)} ⊆
      (Z.intersectStrip C φ y Λ).construct := by -- --- PROOF ---
  rintro x ⟨hx, hs⟩
  set ΛC : Interval (Mat 𝕋 n n) := Interval.matMul (Interval.point Λ) (Interval.point C) with hΛC
  -- the real matrix `I - Λ C` lies in the rounded interval matrix
  have hΛCmem : toRealMat Λ * toRealMat C ∈ ΛC.construct :=
    Interval.matMul_outer (Interval.point Λ) (Interval.point C) (Interval.mem_point Λ)
      (Interval.mem_point C)
  have hA : (1 - toRealMat Λ * toRealMat C : Mat ℝ n n) ∈
      (({ inf := fun i j => subDown (if i = j then one else zero) (ΛC.sup i j)
          sup := fun i j => subUp (if i = j then one else zero) (ΛC.inf i j) } :
        Interval (Mat 𝕋 n n))).construct := by
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    obtain ⟨h₁, h₂⟩ := Interval.mem_mat_iff.mp hΛCmem i j
    have hδ : toReal (if i = j then (one : 𝕋) else zero) = (1 : Mat ℝ n n) i j := by
      by_cases hij : i = j <;> simp [hij, Matrix.one_apply, toReal_one, toReal_zero]
    constructor
    · refine le_trans (subDown_le_sub _ _) ?_
      rw [hδ]
      simp only [Matrix.sub_apply]
      linarith
    · refine le_trans ?_ (sub_le_subUp _ _)
      rw [hδ]
      simp only [Matrix.sub_apply]
      linarith
  -- the part `(I - Λ C) x`
  have h1 := Zonotope.mtimesIntervalMat_outer _ Z
    (Set.mem_iUnion₂.mpr ⟨_, hA, Set.mem_image_of_mem _ hx⟩)
  -- `C x` is a point of the strip zonotope
  let strip : Zonotope (Vec 𝕋 p) :=
    { h := p, c := y, G := fun j i => if i = j then φ i else zero, E := Interval.origin p }
  have hCx : toRealMat C *ᵥ x ∈ strip.construct := by
    refine ⟨toRealMat C *ᵥ x, ?_, 0, ?_, add_zero _⟩
    · -- the coefficients `(C x - y)_i / φ_i` lie in `[-1, 1]` and reach `C x`
      refine Zonotope.mem_nominalSet_iff.mpr ⟨fun i => (toRealMat C *ᵥ x - toRealVec y) i /
        toReal (φ i), fun i => ?_, fun i => ?_⟩
      · have hi := hs i
        have hφ : 0 ≤ toReal (φ i) := le_trans (abs_nonneg _) hi
        by_cases h0 : toReal (φ i) = 0
        · simp [h0]
        · have hpos : 0 < toReal (φ i) := lt_of_le_of_ne hφ (Ne.symm h0)
          simp only [abs_div, abs_of_pos hpos]
          exact (div_le_one hpos).mpr hi
      · -- and they reproduce coordinate `i`
        have hi := hs i
        have hφ : 0 ≤ toReal (φ i) := le_trans (abs_nonneg _) hi
        have hsum : ∑ k, toReal (if i = k then φ i else (zero : 𝕋)) *
            ((toRealMat C *ᵥ x - toRealVec y) k / toReal (φ k)) =
            toReal (φ i) * ((toRealMat C *ᵥ x - toRealVec y) i / toReal (φ i)) := by
          rw [Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk, toReal_zero])
            (by simp)]
          simp
        rw [hsum]
        -- a vanishing `φ_i` forces the residual to vanish too
        by_cases h0 : toReal (φ i) = 0
        · have : (toRealMat C *ᵥ x - toRealVec y) i = 0 := abs_nonpos_iff.mp (h0 ▸ hi)
          simp only [Pi.sub_apply, toRealVec] at this ⊢
          rw [h0]
          linarith
        · rw [mul_div_cancel₀ _ h0]
          simp only [Pi.sub_apply, toRealVec]
          show _ = toReal (y i) + _
          ring
    · have hE : (InflatedContSet.error strip).construct = {0} := Interval.origin_exact p
      rw [hE]
      exact Set.mem_singleton _
  have h2 := Zonotope.mtimes_outer Λ strip ⟨_, hCx, rfl⟩
  refine Zonotope.plus_outer _ _ ⟨_, h1, _, h2, ?_⟩
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

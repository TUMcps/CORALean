module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IsGoodDir
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsBadDirIff
public import CORALean.ContSet.Ellipsoid.Real.Theorems.QuadNonnegOfDominant
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic

@[expose] public section

/-!
# A `true` from `Ellipsoid.isGoodDir` proves the direction is not bad

The test certifies `vᵀ Q₂ v ≤ μ vᵀ Q₁ v` for every `v` (the real quadratic form of the diagonally
dominant `M = μ Q₁ - Q₂`, `Ellipsoid.quad_nonneg_of_dominant`, with every entry of `M` between
the two roundings the test summed) and `μ² lᵀ Q₁ l ≤ lᵀ Q₂ l` (the roundings of `Gᵀ l` squared and
summed in the safe direction). Together they give `p μ ≤ 1` for
`p = sqrt(lᵀ Q₁ l)/sqrt(lᵀ Q₂ l)`, so `vᵀ Q₂ v ≤ vᵀ Q₁ v / p` and the inner shape is positive
semidefinite, which `Ellipsoid.isBadDir_iff` reads as the direction not being bad. A statement
about the nominal ellipsoids, the error boxes aside, under the hypotheses of that theorem.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The nominal shape's entries are the sums of products of the stored rows. -/
theorem Ellipsoid.aux_shape_apply (E : Ellipsoid 𝕋 n) (i j : Fin n) :
    (nominal E).shape i j = ∑ k, toReal (E.G i k) * toReal (E.G j k) := by
  simp [Real.Ellipsoid.shape, Matrix.mul_apply, Matrix.transpose_apply, nominal, toRealMat]

/-- The nominal quadratic form in the direction `l` is the squared entries of `Gᵀ l`. -/
theorem Ellipsoid.aux_quad_apply (E : Ellipsoid 𝕋 n) (l : Vec 𝕋 n) :
    toRealVec l ⬝ᵥ ((nominal E).shape *ᵥ toRealVec l)
      = ∑ k, (∑ i, toReal (l i) * toReal (E.G i k)) ^ 2 := by -- --- PROOF ---
  rw [Real.Ellipsoid.quad_eq]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, nominal, toRealMat, toRealVec]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sq, mul_comm]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => mul_comm _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isGoodDir_sound {E₁ E₂ : Ellipsoid 𝕋 n} {l : Vec 𝕋 n} {μ : 𝕋}
    (h : E₁.isGoodDir E₂ l μ = true) (hr : (nominal E₁).rank = n)
    (hbig : (nominal E₁).isBigger (nominal E₂))
    (hl : 0 < toRealVec l ⬝ᵥ ((nominal E₂).shape *ᵥ toRealVec l)) :
    ¬ (nominal E₁).isBadDir (nominal E₂) (toRealVec l) := by -- --- PROOF ---
  unfold Ellipsoid.isGoodDir at h
  extract_lets qUp qDown mLo mHi dominant cUp cDown aUp bDown at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hμ, hdom⟩, hab⟩ := h
  simp only [dominant, List.all_eq_true, List.mem_finRange, forall_const] at hdom
  have hμ0 : 0 ≤ toReal μ := by simpa [toReal_zero] using toReal_le_of_le hμ
  set μr : ℝ := toReal μ with hμr
  -- the matrix `M = μ Q₁ - Q₂`
  set M : Mat ℝ n n := μr • (nominal E₁).shape - (nominal E₂).shape with hM
  have hMij : ∀ i j, M i j = μr * ∑ k, toReal (E₁.G i k) * toReal (E₁.G j k)
      - ∑ k, toReal (E₂.G i k) * toReal (E₂.G j k) := fun i j => by
    simp only [hM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Ellipsoid.aux_shape_apply E₁, Ellipsoid.aux_shape_apply E₂]
  have hcomm : ∀ (E : Ellipsoid 𝕋 n) (i j : Fin n), ∑ k, toReal (E.G i k) * toReal (E.G j k)
      = ∑ k, toReal (E.G j k) * toReal (E.G i k) := fun E i j =>
    Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hsymm : ∀ i j, M i j = M j i := fun i j => by
    rw [hMij, hMij, hcomm E₁ i j, hcomm E₂ i j]
  -- every entry of `M` lies between its two roundings
  have hlo : ∀ i j, toReal (mLo i j) ≤ M i j := fun i j => by
    rw [hMij]
    have a1 := subDown_le_sub (mulDown μ (qDown E₁ i j)) (qUp E₂ i j)
    have a2 := mulDown_le_mul μ (qDown E₁ i j)
    have a3 : toReal (qDown E₁ i j) ≤ ∑ k, toReal (E₁.G i k) * toReal (E₁.G j k) :=
      dotDown_le _ _
    have a4 : ∑ k, toReal (E₂.G i k) * toReal (E₂.G j k) ≤ toReal (qUp E₂ i j) := le_dotUp _ _
    have a5 := mul_le_mul_of_nonneg_left a3 hμ0
    show toReal (subDown (mulDown μ (qDown E₁ i j)) (qUp E₂ i j)) ≤ _
    linarith
  have hhi : ∀ i j, M i j ≤ toReal (mHi i j) := fun i j => by
    rw [hMij]
    have a1 := sub_le_subUp (mulUp μ (qUp E₁ i j)) (qDown E₂ i j)
    have a2 := mul_le_mulUp μ (qUp E₁ i j)
    have a3 : ∑ k, toReal (E₁.G i k) * toReal (E₁.G j k) ≤ toReal (qUp E₁ i j) := le_dotUp _ _
    have a4 : toReal (qDown E₂ i j) ≤ ∑ k, toReal (E₂.G i k) * toReal (E₂.G j k) :=
      dotDown_le _ _
    have a5 := mul_le_mul_of_nonneg_left a3 hμ0
    show _ ≤ toReal (subUp (mulUp μ (qUp E₁ i j)) (qDown E₂ i j))
    linarith
  -- so `M` is diagonally dominant, and its form is nonnegative
  have hdomR : ∀ i, ∑ j, (if i = j then (0 : ℝ) else |M i j|) ≤ M i i := fun i => by
    have h1 := toReal_le_of_le (hdom i)
    have h3 := sum_le_sumUp
      (fun j => if i = j then (zero : 𝕋) else maximum (mHi i j) (neg (mLo i j)))
    have h4 : ∀ j, (if i = j then (0 : ℝ) else |M i j|)
        ≤ toReal (if i = j then (zero : 𝕋) else maximum (mHi i j) (neg (mLo i j))) := fun j => by
      by_cases hij : i = j
      · simp [hij, toReal_zero]
      · simp only [hij, if_false, toReal_maximum, toReal_neg]
        have b1 := hlo i j
        have b2 := hhi i j
        have b3 := le_max_left (toReal (mHi i j)) (-toReal (mLo i j))
        have b4 := le_max_right (toReal (mHi i j)) (-toReal (mLo i j))
        rw [abs_le]
        constructor <;> linarith
    exact (Finset.sum_le_sum fun j _ => h4 j).trans (h3.trans (h1.trans (hlo i i)))
  have hform : ∀ v : Vec ℝ n, 0 ≤ μr * (v ⬝ᵥ ((nominal E₁).shape *ᵥ v))
      - v ⬝ᵥ ((nominal E₂).shape *ᵥ v) := fun v => by
    have := Real.Ellipsoid.quad_nonneg_of_dominant M hsymm hdomR v
    simpa [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul] using this
  -- the entries of `Gᵀ l` between their roundings
  have hc : ∀ (E : Ellipsoid 𝕋 n) (k : Fin E.k), toReal (cDown E k)
      ≤ ∑ i, toReal (l i) * toReal (E.G i k) ∧ ∑ i, toReal (l i) * toReal (E.G i k)
      ≤ toReal (cUp E k) := fun E k => ⟨dotDown_le _ _, le_dotUp _ _⟩
  set a : ℝ := toRealVec l ⬝ᵥ ((nominal E₁).shape *ᵥ toRealVec l) with ha
  set b : ℝ := toRealVec l ⬝ᵥ ((nominal E₂).shape *ᵥ toRealVec l) with hb
  have ha0 : 0 ≤ a := by
    rw [ha, Ellipsoid.aux_quad_apply]; positivity
  -- `lᵀ Q₁ l` from above
  have haUp : a ≤ toReal aUp := by
    rw [ha, Ellipsoid.aux_quad_apply]
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (sum_le_sumUp _)
    obtain ⟨h1, h2⟩ := hc E₁ k
    have hm : |∑ i, toReal (l i) * toReal (E₁.G i k)|
        ≤ toReal (maximum (cUp E₁ k) (FloatOps.neg (cDown E₁ k))) := by
      rw [toReal_maximum, toReal_neg]
      have b3 := le_max_left (toReal (cUp E₁ k)) (-toReal (cDown E₁ k))
      have b4 := le_max_right (toReal (cUp E₁ k)) (-toReal (cDown E₁ k))
      rw [abs_le]
      constructor <;> linarith
    calc (∑ i, toReal (l i) * toReal (E₁.G i k)) ^ 2
        = |∑ i, toReal (l i) * toReal (E₁.G i k)| ^ 2 := (sq_abs _).symm
      _ ≤ toReal (maximum (cUp E₁ k) (FloatOps.neg (cDown E₁ k))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hm 2
      _ ≤ _ := by
        rw [sq]; exact mul_le_mulUp _ _
  -- `lᵀ Q₂ l` from below
  have hbDown : toReal bDown ≤ b := by
    rw [hb, Ellipsoid.aux_quad_apply]
    refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun k _ => ?_)
    obtain ⟨h1, h2⟩ := hc E₂ k
    -- the safe lower bound `m` of `|(Gᵀ l)_k|` lies between `0` and the entry's magnitude
    set m : 𝕋 := maximum FloatOps.zero (maximum (cDown E₂ k) (FloatOps.neg (cUp E₂ k))) with hm
    have hm1 : 0 ≤ toReal m := by
      rw [hm, toReal_maximum, toReal_zero]; exact le_max_left _ _
    have hm2 : toReal m ≤ |∑ i, toReal (l i) * toReal (E₂.G i k)| := by
      rw [hm, toReal_maximum, toReal_maximum, toReal_neg, toReal_zero]
      refine max_le (abs_nonneg _) (max_le ?_ ?_)
      · exact h1.trans (le_abs_self _)
      · linarith [neg_abs_le (∑ i, toReal (l i) * toReal (E₂.G i k))]
    calc _ ≤ toReal m ^ 2 := by
          rw [sq]; exact mulDown_le_mul _ _
      _ ≤ |∑ i, toReal (l i) * toReal (E₂.G i k)| ^ 2 := pow_le_pow_left₀ hm1 hm2 2
      _ = _ := sq_abs _
  -- so `μ² lᵀ Q₁ l ≤ lᵀ Q₂ l`
  have hμ2 : μr ^ 2 * a ≤ b := by
    have h1 := toReal_le_of_le hab
    have h2 := mul_le_mulUp (mulUp μ μ) aUp
    have h3 := mul_le_mulUp μ μ
    have haUp0 : 0 ≤ toReal aUp := ha0.trans haUp
    have h4 := mul_le_mul_of_nonneg_right h3 haUp0
    have h5 := mul_le_mul_of_nonneg_left haUp (sq_nonneg μr)
    nlinarith
  -- `p μ ≤ 1` and `1 ≤ p` for `p = sqrt a / sqrt b`
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hl
  have hp1 : 1 ≤ Real.sqrt a / Real.sqrt b := by
    rw [le_div_iff₀ hsb, one_mul]
    exact Real.sqrt_le_sqrt (hbig (toRealVec l))
  have hpμ : μr * (Real.sqrt a / Real.sqrt b) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hsb]
    calc μr * Real.sqrt a = Real.sqrt (μr ^ 2 * a) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hμ0]
      _ ≤ Real.sqrt b := Real.sqrt_le_sqrt hμ2
  -- the inner difference shape is positive semidefinite
  rw [Real.Ellipsoid.isBadDir_iff _ _ _ _ hr hbig hl rfl, not_not]
  intro v
  set p : ℝ := Real.sqrt a / Real.sqrt b with hp
  have hppos : 0 < p := by linarith
  have hav : 0 ≤ v ⬝ᵥ ((nominal E₁).shape *ᵥ v) := by
    rw [Real.Ellipsoid.quad_eq, dotProduct_self]; positivity
  have hv := hform v
  have hμp : μr ≤ 1 / p := by rw [le_div_iff₀ hppos]; linarith
  have hbv : v ⬝ᵥ ((nominal E₂).shape *ᵥ v) ≤ (v ⬝ᵥ ((nominal E₁).shape *ᵥ v)) / p := by
    calc _ ≤ μr * (v ⬝ᵥ ((nominal E₁).shape *ᵥ v)) := by linarith
      _ ≤ 1 / p * (v ⬝ᵥ ((nominal E₁).shape *ᵥ v)) := mul_le_mul_of_nonneg_right hμp hav
      _ = _ := by ring
  have hid : (1 - 1 / p) * (v ⬝ᵥ ((nominal E₁).shape *ᵥ v))
      + (1 - p) * (v ⬝ᵥ ((nominal E₂).shape *ᵥ v))
      = (p - 1) * ((v ⬝ᵥ ((nominal E₁).shape *ᵥ v)) / p - v ⬝ᵥ ((nominal E₂).shape *ᵥ v)) := by
    field_simp
    ring
  rw [hid]
  exact mul_nonneg (by linarith) (sub_nonneg.mpr hbv)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

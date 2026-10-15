module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IsGoodDir
public import CORALean.ContSet.Ellipsoid.Float.Theorems.QuadLeQuadUp
public import CORALean.ContSet.Ellipsoid.Float.Theorems.QuadDownLeQuad
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsBadDirIff
public import CORALean.ContSet.Ellipsoid.Real.Theorems.QuadNonnegOfDominant

@[expose] public section

/-!
# A `true` from `Ellipsoid.isGoodDir` proves the direction is not bad

Under the hypotheses both nominal shapes are the stored ones: a refused `Q₁` has rank `0`, and a
refused `Q₂` no positive form. The test certifies `vᵀ Q₂ v ≤ μ vᵀ Q₁ v` for every `v` (the real
quadratic form of the diagonally dominant `M = μ Q₁ - Q₂`, `Ellipsoid.quad_nonneg_of_dominant`,
every entry of `M` between the two roundings the test summed) and `μ² lᵀ Q₁ l ≤ lᵀ Q₂ l`
(`quadUp`, `quadDown`). Together they give `p μ ≤ 1` for `p = sqrt(lᵀ Q₁ l)/sqrt(lᵀ Q₂ l)`, so
`vᵀ Q₂ v ≤ vᵀ Q₁ v / p` and the inner shape is positive semidefinite, which
`Ellipsoid.isBadDir_iff` reads as the direction not being bad. A statement about the nominal
ellipsoids, the error boxes aside, under the hypotheses of that theorem.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isGoodDir_sound {E₁ E₂ : Ellipsoid 𝕋 n} {l : Vec 𝕋 n} {μ : 𝕋}
    (h : E₁.isGoodDir E₂ l μ = true) (hr : (nominal E₁).ellipsoid.rank = n)
    (hbig : (nominal E₁).ellipsoid.isBigger (nominal E₂).ellipsoid)
    (hl : 0 < toRealVec l ⬝ᵥ ((nominal E₂).ellipsoid.Q *ᵥ toRealVec l)) :
    ¬ (nominal E₁).ellipsoid.isBadDir (nominal E₂).ellipsoid (toRealVec l) := by -- --- PROOF ---
  unfold Ellipsoid.isGoodDir at h
  extract_lets mLo mHi dominant at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hμ, hdom⟩, hab⟩ := h
  simp only [dominant, List.all_eq_true, List.mem_finRange, forall_const] at hdom
  have hμ0 : 0 ≤ toReal μ := by simpa [toReal_zero] using toReal_le_of_le hμ
  set μr : ℝ := toReal μ with hμr
  -- both nominal shapes are the stored ones
  have hpsd₂ : (toRealMat E₂.Q).PosSemidef := by
    by_contra hn
    rw [Ellipsoid.nominal_Q_eq, if_neg hn] at hl
    simp at hl
  have hpsd₁ : (toRealMat E₁.Q).PosSemidef := by
    by_contra hn
    have hn0 : n = 0 := by
      rw [← hr]
      show (nominal E₁).ellipsoid.Q.rank = 0
      rw [Ellipsoid.nominal_Q_eq, if_neg hn, Matrix.rank_zero]
    subst hn0
    simp [dotProduct] at hl
  have hN₁ : (nominal E₁).ellipsoid.Q = toRealMat E₁.Q := by rw [Ellipsoid.nominal_of_psd hpsd₁]
  have hN₂ : (nominal E₂).ellipsoid.Q = toRealMat E₂.Q := by rw [Ellipsoid.nominal_of_psd hpsd₂]
  have hsym : ∀ (E : Ellipsoid 𝕋 n), (toRealMat E.Q).PosSemidef →
      ∀ i j, toReal (E.Q i j) = toReal (E.Q j i) := fun E hE i j => by
    have h' := hE.isHermitian.eq
    simp only [conjTranspose_eq_transpose_of_trivial] at h'
    exact (congrFun (congrFun h' i) j).symm
  -- the matrix `M = μ Q₁ - Q₂`, symmetric
  set M : Mat ℝ n n := μr • toRealMat E₁.Q - toRealMat E₂.Q with hM
  have hMij : ∀ i j, M i j = μr * toReal (E₁.Q i j) - toReal (E₂.Q i j) := fun _ _ => rfl
  have hsymm : ∀ i j, M i j = M j i := fun i j => by
    rw [hMij, hMij, hsym E₁ hpsd₁ i j, hsym E₂ hpsd₂ i j]
  -- every entry of `M` lies between its two roundings
  have hlo : ∀ i j, toReal (mLo i j) ≤ M i j := fun i j => by
    rw [hMij]
    have a1 := subDown_le_sub (mulDown μ (E₁.Q i j)) (E₂.Q i j)
    have a2 := mulDown_le_mul μ (E₁.Q i j)
    show toReal (subDown (mulDown μ (E₁.Q i j)) (E₂.Q i j)) ≤ _
    linarith
  have hhi : ∀ i j, M i j ≤ toReal (mHi i j) := fun i j => by
    rw [hMij]
    have a1 := sub_le_subUp (mulUp μ (E₁.Q i j)) (E₂.Q i j)
    have a2 := mul_le_mulUp μ (E₁.Q i j)
    show _ ≤ toReal (subUp (mulUp μ (E₁.Q i j)) (E₂.Q i j))
    linarith
  -- so `M` is diagonally dominant, and its form is nonnegative
  have hdomR : ∀ i, ∑ j, (if i = j then (0 : ℝ) else |M i j|) ≤ M i i := fun i => by
    have h1 := toReal_le_of_le (hdom i)
    -- each off-diagonal `|Mᵢⱼ|` below its rounded bound, summed upward
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
  have hform : ∀ v : Vec ℝ n, 0 ≤ μr * (v ⬝ᵥ ((nominal E₁).ellipsoid.Q *ᵥ v))
      - v ⬝ᵥ ((nominal E₂).ellipsoid.Q *ᵥ v) := fun v => by
    have := Real.Ellipsoid.quad_nonneg_of_dominant M hsymm hdomR v
    rw [hN₁, hN₂]
    simpa [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul] using this
  -- the two forms in the direction `l`
  set a : ℝ := toRealVec l ⬝ᵥ ((nominal E₁).ellipsoid.Q *ᵥ toRealVec l) with ha
  set b : ℝ := toRealVec l ⬝ᵥ ((nominal E₂).ellipsoid.Q *ᵥ toRealVec l) with hb
  have ha0 : 0 ≤ a := by
    rw [ha, hN₁]
    simpa using hpsd₁.dotProduct_mulVec_nonneg (toRealVec l)
  -- `lᵀ Q₁ l` from above, `lᵀ Q₂ l` from below
  have haUp : a ≤ toReal (E₁.quadUp l) := by rw [ha, hN₁]; exact E₁.quad_le_quadUp l
  have hbDown : toReal (E₂.quadDown l) ≤ b := by rw [hb, hN₂]; exact E₂.quadDown_le_quad l
  -- so `μ² lᵀ Q₁ l ≤ lᵀ Q₂ l`
  have hμ2 : μr ^ 2 * a ≤ b := by
    have h1 := toReal_le_of_le hab
    have h2 := mul_le_mulUp (mulUp μ μ) (E₁.quadUp l)
    have h3 := mul_le_mulUp μ μ
    have haUp0 : 0 ≤ toReal (E₁.quadUp l) := ha0.trans haUp
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
  -- `vᵀ Q₂ v ≤ vᵀ Q₁ v / p`, from `μ ≤ 1/p` and the dominance
  have hppos : 0 < p := by linarith
  have hav : 0 ≤ v ⬝ᵥ ((nominal E₁).ellipsoid.Q *ᵥ v) := by
    rw [hN₁]
    simpa using hpsd₁.dotProduct_mulVec_nonneg v
  have hv := hform v
  have hμp : μr ≤ 1 / p := by rw [le_div_iff₀ hppos]; linarith
  have hbv : v ⬝ᵥ ((nominal E₂).ellipsoid.Q *ᵥ v) ≤ (v ⬝ᵥ ((nominal E₁).ellipsoid.Q *ᵥ v)) / p := by
    calc _ ≤ μr * (v ⬝ᵥ ((nominal E₁).ellipsoid.Q *ᵥ v)) := by linarith
      _ ≤ 1 / p * (v ⬝ᵥ ((nominal E₁).ellipsoid.Q *ᵥ v)) := mul_le_mul_of_nonneg_right hμp hav
      _ = _ := by ring
  -- the difference shape's form, factored
  have hid : (1 - 1 / p) * (v ⬝ᵥ ((nominal E₁).ellipsoid.Q *ᵥ v))
      + (1 - p) * (v ⬝ᵥ ((nominal E₂).ellipsoid.Q *ᵥ v))
      = (p - 1) * ((v ⬝ᵥ ((nominal E₁).ellipsoid.Q *ᵥ v)) / p
        - v ⬝ᵥ ((nominal E₂).ellipsoid.Q *ᵥ v)) := by
    field_simp
    ring
  rw [hid]
  exact mul_nonneg (by linarith) (sub_nonneg.mpr hbv)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

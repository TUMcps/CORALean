module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Ellipsoid.Float.Operations.IntersectStripGollamudi
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ExistsBallOfStrip
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AddSubMemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.InflateSubPosSemidef
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsPsdSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.QuadLeQuadUp
public import CORALean.ContSet.Ellipsoid.Float.Theorems.QuadDownLeQuad
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructOfFactor
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

@[expose] public section

/-!
# The float Gollamudi update encloses the intersection with one strip

Outer: every point of `E` with `|c x - y| ≤ φ` lies in
`Ellipsoid.intersectStripGollamudi steps E c φ y λ`, for every `λ`, `steps` and input, with no
positive-definiteness or invertibility hypothesis; a `Q` not certified positive semi-definite, a
`λ` outside `[0, 1)` or a failed check returns `E` itself. A point `x = q + G u + e` of `E`,
`G = Q^(1/2)`, satisfies `|vᵀ u - δ| ≤ φ'` for `v = G cᵀ`, the stored `δ` and the widened `φ'`,
so `Ellipsoid.exists_ball_of_strip` writes `u = κ v + α w + β (vᵀ w) v` with `‖w‖₂ ≤ 1`, every
hypothesis of it read off a directed rounding (`ν = vᵀ v = c Q cᵀ` through `quadUp`/`quadDown`).
Then `x = q + κ W + G N w + e`, `W = G v = Q cᵀ`: the stored center plus its rounding, a point of
the ellipsoid of `G N (G N)ᵀ = α² Q + (2αβ + β²ν) W Wᵀ`, which the stored shape dominates
(`inflate_sub_posSemidef`), and `e`. Not exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A product of two bracketed factors lies between the float corner hulls. -/
theorem Ellipsoid.aux_mul_mem_corners {a b c d : 𝕋} {y x : ℝ} (hy₁ : toReal a ≤ y)
    (hy₂ : y ≤ toReal b) (hx₁ : toReal c ≤ x) (hx₂ : x ≤ toReal d) :
    toReal (Interval.mulLo a b c d) ≤ y * x ∧ y * x ≤ toReal (Interval.mulHi a b c d) := by
  have h := Real.Interval.mul_between_corners hy₁ hy₂ hx₁ hx₂
  exact ⟨le_trans (Interval.mulLo_le a b c d) h.1, le_trans h.2 (Interval.le_mulHi a b c d)⟩

/-- A quotient of bracketed numerator by a positive bracketed divisor lies between the corner
quotients of the numerator's ends. -/
theorem Ellipsoid.aux_div_between {aLo a aHi sLo s sHi : ℝ} (hs₀ : 0 < sLo) (hs₁ : sLo ≤ s)
    (hs₂ : s ≤ sHi) (ha₁ : aLo ≤ a) (ha₂ : a ≤ aHi) :
    min (aLo / sLo) (aLo / sHi) ≤ a / s
      ∧ a / s ≤ max (aHi / sLo) (aHi / sHi) := by -- --- PROOF ---
  have hs : 0 < s := lt_of_lt_of_le hs₀ hs₁
  have hsH : 0 < sHi := lt_of_lt_of_le hs hs₂
  constructor
  · refine le_trans ?_ (div_le_div_of_nonneg_right ha₁ hs.le)
    rcases le_total 0 aLo with h | h
    · exact min_le_of_right_le (div_le_div_of_nonneg_left h hs hs₂)
    · refine min_le_of_left_le ?_
      rw [div_le_div_iff₀ hs₀ hs]
      nlinarith
  · refine le_trans (div_le_div_of_nonneg_right ha₂ hs.le) ?_
    rcases le_total 0 aHi with h | h
    · exact le_max_of_le_left (div_le_div_of_nonneg_left h hs₀ hs₁)
    · refine le_max_of_le_right ?_
      rw [div_le_div_iff₀ hs hsH]
      nlinarith

/-- `S ≤ r² a` from a rounded-up quotient and a rounded-up root of it. -/
theorem Ellipsoid.aux_le_sq_mul {S a q r : ℝ} (ha : 0 < a) (hq : S / a ≤ q)
    (hr : Real.sqrt q ≤ r) : S ≤ r ^ 2 * a := by -- --- PROOF ---
  rcases le_or_gt S 0 with hS | hS
  · nlinarith [sq_nonneg r]
  have h0 : 0 ≤ S / a := (div_pos hS ha).le
  have h1 : Real.sqrt (S / a) ≤ r := le_trans (Real.sqrt_le_sqrt hq) hr
  have h2 : S / a ≤ r ^ 2 := by
    rw [← Real.sq_sqrt h0]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [div_le_iff₀ ha] at h2
  exact h2


/-- The strip in the factor vector: `x = q + G u + e` with `|c x - y| ≤ φ` gives
`|vᵀ u - δ| ≤ φ'` for `v = G cᵀ` (`G` symmetric) and the stored `δ`, `φ` widened by the box and
the rounding gap of `δ`. -/
theorem Ellipsoid.aux_strip_widen (E : Ellipsoid 𝕋 n) (c : Vec 𝕋 n) (φ y : 𝕋) {G : Mat ℝ n n}
    (hG : Gᵀ = G) {u e : Vec ℝ n}
    (he : ∀ i, toReal (E.I_error.inf i) ≤ e i ∧ e i ≤ toReal (E.I_error.sup i))
    (hx : |∑ i, toReal (c i) * (toReal (E.q i) + (G *ᵥ u) i + e i) - toReal y| ≤ toReal φ) :
    let box := dotUp (fun i => absolute (c i))
      (fun i => maximum (absolute (E.I_error.inf i)) (absolute (E.I_error.sup i)))
    let δs := subDown y (dotUp c E.q)
    |(G *ᵥ toRealVec c) ⬝ᵥ u - toReal δs|
      ≤ toReal (addUp (addUp φ box) (subUp (subUp y (dotDown c E.q)) δs)) := by -- --- PROOF ---
  intro box δs
  -- the exact `δ` and its rounding gap
  set δt := toReal y - ∑ i, toReal (c i) * toReal (E.q i) with hδt
  have hδ₁ : toReal (subDown y (dotUp c E.q)) ≤ δt :=
    le_trans (subDown_le_sub _ _) (sub_le_sub_left (le_dotUp c E.q) _)
  have hδ₂ : δt - toReal (subDown y (dotUp c E.q))
      ≤ toReal (subUp (subUp y (dotDown c E.q)) (subDown y (dotUp c E.q))) := le_trans
    (sub_le_sub_right (le_trans (sub_le_sub_left (dotDown_le c E.q) _) (sub_le_subUp _ _)) _)
    (sub_le_subUp _ _)
  -- the box through `c`
  set ce := ∑ i, toReal (c i) * e i with hce
  have hce₁ : |ce| ≤ toReal box := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (le_dotUp _ _))
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, toReal_absolute]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs (he i).1 (he i).2
  -- `vᵀ u = c G u`, `G` symmetric
  have hvu : (G *ᵥ toRealVec c) ⬝ᵥ u = ∑ i, toReal (c i) * (G *ᵥ u) i := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hG, dotProduct_comm]
    rfl
  have hcx : ∑ i, toReal (c i) * (toReal (E.q i) + (G *ᵥ u) i + e i) - toReal y
      = (G *ᵥ toRealVec c) ⬝ᵥ u - δt + ce := by
    rw [hvu]
    simp only [mul_add, Finset.sum_add_distrib, hδt, hce]
    ring
  -- `φ'` is above the two widenings, and each part is bounded
  have hφ₁ := add_le_addUp φ box
  have hφ₂ := add_le_addUp (addUp φ box) (subUp (subUp y (dotDown c E.q)) δs)
  have a1 := abs_le.mp hx
  have a2 := abs_le.mp hce₁
  rw [hcx] at a1
  rw [abs_le]
  constructor <;> linarith


/-- `λ`, `s = 1 - λ + λ ν` and `sigma_sq` against their directed roundings, `ν` between its
own. -/
theorem Ellipsoid.aux_strip_scalars {ν : ℝ} {lam δ φ' om omHi νLo νHi sLo sHi corr
    S : 𝕋} (hl0 : 0 ≤ toReal lam) (hom : 0 < toReal om) (h_om : om = subDown FloatOps.one lam)
    (h_omHi : omHi = subUp FloatOps.one lam) (hν0 : 0 ≤ ν) (hνLo : toReal νLo ≤ ν)
    (hνHi : ν ≤ toReal νHi)
    (h_sLo : sLo = maximum om (addDown om (mulDown lam νLo)))
    (h_sHi : sHi = addUp omHi (mulUp lam νHi))
    (h_corr : corr = divDown (mulDown (maximum FloatOps.zero (mulDown lam om))
      (maximum FloatOps.zero (mulDown δ δ))) sHi)
    (h_S : S = subUp (addUp omHi (mulUp lam (mulUp φ' φ'))) corr) : -- --- STMT ---
    toReal om ≤ 1 - toReal lam
      ∧ 0 < toReal sLo ∧ toReal sLo ≤ 1 - toReal lam + toReal lam * ν
      ∧ 1 - toReal lam + toReal lam * ν ≤ toReal sHi
      ∧ 1 - toReal lam + toReal lam * toReal φ' ^ 2 - toReal lam * (1 - toReal lam)
          * toReal δ ^ 2 / (1 - toReal lam + toReal lam * ν)
        ≤ toReal S := by -- --- PROOF ---
  set l := toReal lam with hl
  have hom₁ : toReal om ≤ 1 - l := by
    have := subDown_le_sub FloatOps.one lam; rwa [toReal_one, ← h_om] at this
  have hom₂ : 1 - l ≤ toReal omHi := by
    have := sub_le_subUp FloatOps.one lam; rwa [toReal_one, ← h_omHi] at this
  -- `s` between its roundings
  set s := 1 - l + l * ν with hs
  have hlν : 0 ≤ l * ν := mul_nonneg hl0 hν0
  have hsLo₀ : 0 < toReal sLo := by
    rw [h_sLo, toReal_maximum]; exact lt_of_lt_of_le hom (le_max_left _ _)
  have hsLo : toReal sLo ≤ s := by
    rw [h_sLo, toReal_maximum]
    refine max_le (by linarith) (le_trans (addDown_le_add _ _) ?_)
    have h1 := mulDown_le_mul lam νLo
    have h2 := mul_le_mul_of_nonneg_left hνLo hl0
    linarith
  have hsHi : s ≤ toReal sHi := by
    rw [h_sHi]
    refine le_trans ?_ (add_le_addUp _ _)
    have h1 := mul_le_mulUp lam νHi
    have h2 := mul_le_mul_of_nonneg_left hνHi hl0
    linarith
  have hs0 : 0 < s := lt_of_lt_of_le hsLo₀ hsLo
  have hsH0 : 0 < toReal sHi := lt_of_lt_of_le hs0 hsHi
  refine ⟨hom₁, hsLo₀, hsLo, hsHi, ?_⟩
  -- `sigma_sq ≤ S`
  have hφ2 : l * toReal φ' ^ 2 ≤ toReal (mulUp lam (mulUp φ' φ')) := by
    refine le_trans ?_ (mul_le_mulUp _ _)
    rw [sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mulUp _ _) hl0
  have hll : 0 ≤ l * (1 - l) := mul_nonneg hl0 (by linarith)
  have hT : 0 ≤ l * (1 - l) * toReal δ ^ 2 := mul_nonneg hll (sq_nonneg _)
  -- the subtracted `λ (1 - λ) δ² / s`, from below, each factor clamped at `0`
  have hP1 : 0 ≤ toReal (maximum FloatOps.zero (mulDown lam om))
      ∧ toReal (maximum FloatOps.zero (mulDown lam om)) ≤ l * (1 - l) := by
    rw [toReal_maximum, toReal_zero]
    exact ⟨le_max_left _ _, max_le hll
      (le_trans (mulDown_le_mul _ _) (mul_le_mul_of_nonneg_left hom₁ hl0))⟩
  have hP2 : 0 ≤ toReal (maximum FloatOps.zero (mulDown δ δ))
      ∧ toReal (maximum FloatOps.zero (mulDown δ δ)) ≤ toReal δ ^ 2 := by
    rw [toReal_maximum, toReal_zero]
    exact ⟨le_max_left _ _, max_le (sq_nonneg _) ((mulDown_le_mul _ _).trans_eq (sq _).symm)⟩
  have hPm : toReal (mulDown (maximum FloatOps.zero (mulDown lam om))
      (maximum FloatOps.zero (mulDown δ δ))) ≤ l * (1 - l) * toReal δ ^ 2 :=
    le_trans (mulDown_le_mul _ _) (mul_le_mul hP1.2 hP2.2 hP2.1 (le_trans hP1.1 hP1.2))
  -- divided by `sHi ≥ s`, whatever the numerator's sign
  have hcorr : toReal corr ≤ l * (1 - l) * toReal δ ^ 2 / s := by
    rw [h_corr]
    refine le_trans (divDown_le_div _ _ hsH0) ?_
    rcases le_total (toReal (mulDown (maximum FloatOps.zero (mulDown lam om))
      (maximum FloatOps.zero (mulDown δ δ)))) 0 with h | h
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg h hsH0.le) (div_nonneg hT hs0.le)
    · exact le_trans (div_le_div_of_nonneg_left h hs0 hsHi)
        (div_le_div_of_nonneg_right hPm hs0.le)
  have h1 := add_le_addUp omHi (mulUp lam (mulUp φ' φ'))
  have h2 := sub_le_subUp (addUp omHi (mulUp lam (mulUp φ' φ'))) corr
  rw [h_S]
  linarith

/-- The generator factor's conditions, from the two upward square roots and the check
`g ≤ γ_lo`, `0 < γ_lo`: `0 < α`, `0 < α + β ν`, `S ≤ α² (1 - λ)`, `S ≤ (α + β ν)² s`. -/
theorem Ellipsoid.aux_strip_factor {S om sLo νHi g α β γLo : 𝕋} {l ν s : ℝ} (steps : ℕ)
    (hom : 0 < toReal om) (hom₁ : toReal om ≤ 1 - l) (hν0 : 0 ≤ ν) (hνHi : ν ≤ toReal νHi)
    (hsLo₀ : 0 < toReal sLo) (hsLo : toReal sLo ≤ s)
    (h_α : α = sqrtUp steps (divUp S om)) (h_g : g = sqrtUp steps (divUp S sLo))
    (hβ : toReal β ≤ 0) (h_γLo : γLo = addDown α (mulDown β νHi)) (hγLo : 0 < toReal γLo)
    (hgγ : toReal g ≤ toReal γLo) : -- --- STMT ---
    0 < toReal α ∧ 0 < toReal α + toReal β * ν ∧ toReal S ≤ toReal α ^ 2 * (1 - l)
      ∧ toReal S ≤ (toReal α + toReal β * ν) ^ 2 * s := by -- --- PROOF ---
  have hγ₁ : toReal γLo ≤ toReal α + toReal β * ν := by
    rw [h_γLo]
    refine le_trans (addDown_le_add _ _) (add_le_add le_rfl ?_)
    exact le_trans (mulDown_le_mul _ _) (mul_le_mul_of_nonpos_left hνHi hβ)
  have hγ : 0 < toReal α + toReal β * ν := lt_of_lt_of_le hγLo hγ₁
  have hβν : toReal β * ν ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hβ hν0
  have hs0 : 0 < s := lt_of_lt_of_le hsLo₀ hsLo
  refine ⟨by linarith, hγ, ?_, ?_⟩
  · have h := Ellipsoid.aux_le_sq_mul hom (div_le_divUp S om hom)
      (show _ ≤ toReal α by rw [h_α]; exact le_sqrtUp steps _)
    have := mul_le_mul_of_nonneg_left hom₁ (sq_nonneg (toReal α))
    linarith
  · rcases le_or_gt (toReal S) 0 with hS | hS
    · have := mul_nonneg (sq_nonneg (toReal α + toReal β * ν)) hs0.le
      linarith
    have hq : toReal S / s ≤ toReal (divUp S sLo) :=
      le_trans (div_le_div_of_nonneg_left hS.le hsLo₀ hsLo) (div_le_divUp S sLo hsLo₀)
    exact Ellipsoid.aux_le_sq_mul hs0 hq
      (le_trans (by rw [h_g]; exact le_sqrtUp steps _) (le_trans hgγ hγ₁))

/-- The factor `G N`, `N = α I + β v vᵀ`, `v = G cᵀ`: its value at `w` is `α G w + β (vᵀ w) W`,
and its Gram matrix `α² Q + (2αβ + β² vᵀv) W Wᵀ`, `W = G v = Q cᵀ`. -/
theorem Ellipsoid.aux_strip_shape {G Q : Mat ℝ n n} (hG : Gᵀ = G) (hGG : G * G = Q)
    (cr : Vec ℝ n) (α β : ℝ) : -- --- STMT ---
    let v := G *ᵥ cr
    let W := Q *ᵥ cr
    let N : Mat ℝ n n := α • 1 + β • vecMulVec v v
    (∀ w, (G * N) *ᵥ w = α • (G *ᵥ w) + (β * (v ⬝ᵥ w)) • W)
      ∧ ∀ i j, ((G * N) * (G * N)ᵀ) i j
        = α * α * Q i j + (α * β + α * β + β * β * (v ⬝ᵥ v)) * (W i * W j) := by -- --- PROOF ---
  intro v W N
  have hGv : G *ᵥ v = W := by rw [mulVec_mulVec, hGG]
  -- `G N = α G + β W vᵀ`
  have hGN : G * N = α • G + β • vecMulVec W v := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, ← hGv]
    congr 1
    ext i j
    simp [Matrix.mul_apply, vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  refine ⟨fun w => ?_, fun i j => ?_⟩
  · rw [hGN, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    congr 1
    funext i
    simp [vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm]
    exact Finset.sum_congr rfl fun k _ => by ring
  · -- the Gram matrix, entry by entry
    have hQ : ∀ i j, ∑ k, G i k * G j k = Q i j := fun i j => by
      rw [← hGG, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by
        rw [show G j k = G k j from congrFun (congrFun hG k) j]
    have hW : ∀ i, ∑ k, G i k * v k = W i := fun i => by rw [← hGv]; rfl
    rw [hGN]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, vecMulVec_apply]
    have e : ∀ k, (α * G i k + β * (W i * v k)) * (α * G j k + β * (W j * v k))
        = α * α * (G i k * G j k) + α * β * W j * (G i k * v k) + α * β * W i * (G j k * v k)
          + β * β * (W i * W j) * (v k * v k) := fun k => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hQ, hW]
    simp only [dotProduct]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.intersectStripGollamudi_outer (steps : ℕ) (E : Ellipsoid 𝕋 n) (c : Vec 𝕋 n)
    (φ y lam : 𝕋) :
    E.construct ∩ {x | |∑ i, toReal (c i) * x i - toReal y| ≤ toReal φ}
      ⊆ (Ellipsoid.intersectStripGollamudi steps E c φ y lam).construct := by -- --- PROOF ---
  rintro x ⟨hxE, hxS⟩
  unfold Ellipsoid.intersectStripGollamudi
  extract_lets wLoV wHiV wLo wHi δ eδ mag φ' νLo νHi om omHi sLo sHi corr S α g β γLo aLo aHi
    κLo κHi qLo qHi b2νLo b2νHi μLo μHi X
  split_ifs with hc
  swap
  · exact hxE
  obtain ⟨hl0, hom, hγLo, hgγ, hpsd⟩ := hc
  rw [Ellipsoid.materialise_eq]
  -- the checks, read as reals
  have hl0' : 0 ≤ toReal lam := by
    have := toReal_le_of_le hl0; rwa [toReal_zero] at this
  have hom' : 0 < toReal om := by
    have := toReal_lt_of_ltStrict hom; rwa [toReal_zero] at this
  have hγLo' : 0 < toReal γLo := by
    have := toReal_lt_of_ltStrict hγLo; rwa [toReal_zero] at this
  have hQ := Ellipsoid.posSemidef_of_isPsd hpsd
  -- the point: `x = q + G u + e`, `G = Q^(1/2)`
  set Er : Real.Ellipsoid n := ⟨toRealMat E.Q, toRealVec E.q, hQ⟩ with hEr
  set G := Er.G with hGdef
  have hGt : Gᵀ = G := Er.G_transpose
  have hGG : G * G = toRealMat E.Q := by
    have h := Er.G_mul_transpose
    rwa [Er.G_transpose] at h
  obtain ⟨xn, hxn, e, he, rfl⟩ := hxE
  have hxn' : xn ∈ Er.construct := by
    have h : xn ∈ (nominal E).ellipsoid.construct := hxn
    rwa [Ellipsoid.nominal_of_psd hQ] at h
  obtain ⟨u, hu, rfl⟩ := Real.Ellipsoid.mem_construct_iff.1 hxn'
  have he' : ∀ i, toReal (E.I_error.inf i) ≤ e i ∧ e i ≤ toReal (E.I_error.sup i) := fun i => he i
  have hxS' : |∑ i, toReal (c i) * (toReal (E.q i) + (G *ᵥ u) i + e i) - toReal y|
      ≤ toReal φ := hxS
  -- `v = G cᵀ`, `ν = vᵀ v = c Q cᵀ` between its roundings, and `W = G v = Q cᵀ`
  obtain ⟨hNw, hNN⟩ := Ellipsoid.aux_strip_shape hGt hGG (toRealVec c) (toReal α) (toReal β)
  set v := G *ᵥ toRealVec c with hv
  set ν := v ⬝ᵥ v with hν
  set W := toRealMat E.Q *ᵥ toRealVec c with hWdef
  have hν0 : 0 ≤ ν := by rw [hν, dotProduct_self]; positivity
  have hνQ : ν = toRealVec c ⬝ᵥ (toRealMat E.Q *ᵥ toRealVec c) := by
    rw [hν, hv, dotProduct_mulVec, ← mulVec_transpose, hGt, mulVec_mulVec, hGG, dotProduct_comm]
  have hνHi : ν ≤ toReal νHi := by rw [hνQ]; exact E.quad_le_quadUp c
  have hνLo : toReal νLo ≤ ν := by
    simp only [νLo, toReal_maximum, toReal_zero]
    exact max_le hν0 (by rw [hνQ]; exact E.quadDown_le_quad c)
  have hW₁ : ∀ i, toReal (wLo i) ≤ W i ∧ W i ≤ toReal (wHi i) := fun i => by
    simp only [wLo, wHi, wLoV, wHiV, Vector.getElem_ofFn]
    exact ⟨dotDown_le (E.Q i) c, le_dotUp (E.Q i) c⟩
  -- the strip in the factor vector, and the scalars
  have hstrip := Ellipsoid.aux_strip_widen E c φ y hGt he' hxS'
  obtain ⟨hom₁, hsLo₀, hsLo, hsHi, hσ⟩ := Ellipsoid.aux_strip_scalars (δ := δ)
    (φ' := φ') hl0' hom' rfl rfl hν0 hνLo hνHi rfl rfl rfl rfl
  have hβ : toReal β ≤ 0 := by
    simp only [β]
    split_ifs
    · rw [toReal_minimum, toReal_zero]; exact min_le_left _ _
    · rw [toReal_zero]
  obtain ⟨hα, hγ, hSα, hSγ⟩ := Ellipsoid.aux_strip_factor (S := S) steps hom' hom₁ hν0 hνHi
    hsLo₀ hsLo rfl rfl hβ rfl hγLo' (toReal_le_of_le hgγ)
  obtain ⟨w, hw, huw⟩ := Ellipsoid.exists_ball_of_strip (v := v) (u := u) hl0'
    (by linarith) hu hstrip hσ hα hγ hSα hSγ
  -- `κ = λ δ / s`, between its roundings
  set κ := toReal lam * toReal δ / (1 - toReal lam + toReal lam * ν) with hκ
  have hsHi₀ := lt_of_lt_of_le (lt_of_lt_of_le hsLo₀ hsLo) hsHi
  have hκ₁ : toReal κLo ≤ κ ∧ κ ≤ toReal κHi := by
    have hb := Ellipsoid.aux_div_between hsLo₀ hsLo hsHi (mulDown_le_mul lam δ)
      (mul_le_mulUp lam δ)
    have d1 := divDown_le_div aLo sLo hsLo₀
    have d2 := divDown_le_div aLo sHi hsHi₀
    have d3 := div_le_divUp aHi sLo hsLo₀
    have d4 := div_le_divUp aHi sHi hsHi₀
    simp only [κLo, κHi, toReal_minimum, toReal_maximum]
    exact ⟨le_trans (min_le_min d1 d2) hb.1, le_trans hb.2 (max_le_max d3 d4)⟩
  -- the new nominal point `G N w`, in the ellipsoid of `G N (G N)ᵀ`
  set N : Mat ℝ n n := toReal α • 1 + toReal β • vecMulVec v v with hN
  set F := Real.Ellipsoid.ofFactor (G * N) 0 with hF
  have hyF : (G * N) *ᵥ w ∈ F.construct := by
    rw [hF, Real.Ellipsoid.construct_ofFactor]
    exact ⟨w, hw, by rw [zero_add]⟩
  -- the interval matrix holds `F.Q`, entry by entry
  have hμ : toReal μLo ≤ toReal α * toReal β + toReal α * toReal β + toReal β * toReal β * ν
      ∧ toReal α * toReal β + toReal α * toReal β + toReal β * toReal β * ν ≤ toReal μHi := by
    have hb2 := Ellipsoid.aux_mul_mem_corners (mulDown_le_mul β β) (mul_le_mulUp β β) hνLo hνHi
    have m1 := mulDown_le_mul α β
    have m2 := mul_le_mulUp α β
    have a1 := addDown_le_add (mulDown α β) (mulDown α β)
    have a2 := addDown_le_add (addDown (mulDown α β) (mulDown α β)) b2νLo
    have a3 := add_le_addUp (mulUp α β) (mulUp α β)
    have a4 := add_le_addUp (addUp (mulUp α β) (mulUp α β)) b2νHi
    exact ⟨by simp only [μLo, b2νLo] at *; linarith, by simp only [μHi, b2νHi] at *; linarith⟩
  have hX : ∀ i j, toReal (X.inf i j) ≤ F.Q i j ∧ F.Q i j ≤ toReal (X.sup i j) := by
    intro i j
    -- `α² Q + μ W Wᵀ`, each product between its corners
    have hFQ : F.Q i j = toReal α * toReal α * toReal (E.Q i j)
        + (toReal α * toReal β + toReal α * toReal β + toReal β * toReal β * ν)
          * (W i * W j) := hNN i j
    rw [hFQ]
    have h1 := Ellipsoid.aux_mul_mem_corners (mulDown_le_mul α α) (mul_le_mulUp α α)
      (le_refl (toReal (E.Q i j))) (le_refl (toReal (E.Q i j)))
    have hWW := Ellipsoid.aux_mul_mem_corners (hW₁ i).1 (hW₁ i).2 (hW₁ j).1 (hW₁ j).2
    have h2 := Ellipsoid.aux_mul_mem_corners hμ.1 hμ.2 hWW.1 hWW.2
    have a1 := addDown_le_add
      (Interval.mulLo (mulDown α α) (mulUp α α) (E.Q i j) (E.Q i j))
      (Interval.mulLo μLo μHi (Interval.mulLo (wLo i) (wHi i) (wLo j) (wHi j))
        (Interval.mulHi (wLo i) (wHi i) (wLo j) (wHi j)))
    have a2 := add_le_addUp
      (Interval.mulHi (mulDown α α) (mulUp α α) (E.Q i j) (E.Q i j))
      (Interval.mulHi μLo μHi (Interval.mulLo (wLo i) (wHi i) (wLo j) (wHi j))
        (Interval.mulHi (wLo i) (wHi i) (wLo j) (wHi j)))
    exact ⟨by simp only [X]; linarith, by simp only [X]; linarith⟩
  -- `F.Q` symmetric, so the inflated matrix dominates it and `F` lies in the nominal part
  have hsym : ∀ i j, F.Q i j = F.Q j i := fun i j => by
    have h := F.psd.isHermitian.eq
    simp only [conjTranspose_eq_transpose_of_trivial] at h
    exact (congrFun (congrFun h i) j).symm
  have hdom := Ellipsoid.inflate_sub_posSemidef hX hsym
  have hmem := Ellipsoid.add_sub_mem_nominalSet
    (E := ⟨Ellipsoid.inflate X, qLo, E.I_error.plus (Interval.residual qLo qHi qLo)⟩)
    (Or.inr hdom) hyF
  -- the center's rounding, which the residual box holds
  have hr : (fun i => toReal (E.q i) + κ * W i - toReal (qLo i))
      ∈ (Interval.residual qLo qHi qLo).construct := by
    refine Interval.sub_mem_residual (x := fun i => toReal (E.q i) + κ * W i) fun i => ?_
    have hm := Ellipsoid.aux_mul_mem_corners hκ₁.1 hκ₁.2 (hW₁ i).1 (hW₁ i).2
    have a1 := addDown_le_add (E.q i) (Interval.mulLo κLo κHi (wLo i) (wHi i))
    have a2 := add_le_addUp (E.q i) (Interval.mulHi κLo κHi (wLo i) (wHi i))
    exact ⟨by simp only [qLo]; linarith, by simp only [qHi]; linarith⟩
  refine ⟨_, hmem, _, Interval.plus_outer _ _ ⟨e, he, _, hr, rfl⟩, ?_⟩
  -- `q + G u = q + κ W + G N w`
  have hGu : G *ᵥ u = κ • W + (G * N) *ᵥ w := by
    rw [hNw w, huw, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul]
    have hGv : G *ᵥ v = W := by rw [hv, mulVec_mulVec, hGG]
    rw [hGv, add_assoc]
  funext i
  have hi := congrFun hGu i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hi ⊢
  show toReal (qLo i) + ((G * N) *ᵥ w - 0) i + (e i + (toReal (E.q i) + κ * W i - toReal (qLo i)))
    = toReal (E.q i) + (G *ᵥ u) i + e i
  rw [hi]
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

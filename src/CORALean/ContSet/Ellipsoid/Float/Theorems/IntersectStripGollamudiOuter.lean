module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IntersectStripGollamudi
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ExistsBallOfStrip
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemGeneratorError
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
positive-definiteness or invertibility hypothesis; a `λ` outside `[0, 1)` or a failed generator
check returns `E` itself. A point `x = E.c + G u + e` of `E` satisfies `|vᵀ u - δ| ≤ φ'` for the
stored `v`, `δ` and the widened `φ'` (the box and the two rounding gaps), so
`Ellipsoid.exists_ball_of_strip` writes `u = κ v + α w + β (vᵀ w) v` with `‖w‖₂ ≤ 1`, every
hypothesis of it read off a directed rounding. Then `x` is the stored center and generators at
`w`, plus the center's and the generators' rounding gaps, plus `e`, each in its part of the new box.
Not exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
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


/-- The strip in the factor vector: `x = E.c + G u + e` with `|c x - y| ≤ φ` gives
`|vᵀ u - δ| ≤ φ'` for the stored `v` and `δ`, `φ` widened by the box and the two rounding gaps. -/
theorem Ellipsoid.aux_strip_widen (E : Ellipsoid 𝕋 n) (c : Vec 𝕋 n) (φ y : 𝕋) {u : Vec ℝ E.k}
    {e : Vec ℝ n} (hu : ‖u‖₂ ≤ 1)
    (he : ∀ i, toReal (E.I_error.inf i) ≤ e i ∧ e i ≤ toReal (E.I_error.sup i))
    (hx : |∑ i, toReal (c i) * (toReal (E.c i) + ∑ j, toReal (E.G i j) * u j + e i)
      - toReal y| ≤ toReal φ)
    {v ev : Vec 𝕋 E.k} (hv : ∀ j, v j = dotDown (fun i => E.G i j) c)
    (hev : ∀ j, ev j = subUp (dotUp (fun i => E.G i j) c) (v j)) :
    let box := dotUp (fun i => absolute (c i))
      (fun i => maximum (absolute (E.I_error.inf i)) (absolute (E.I_error.sup i)))
    let δs := subDown y (dotUp c E.c)
    |toRealVec v ⬝ᵥ u - toReal δs|
      ≤ toReal (addUp (addUp (addUp φ box) (sumUp ev))
          (subUp (subUp y (dotDown c E.c)) δs)) := by -- --- PROOF ---
  intro box δs
  -- the exact `v` and its rounding gap
  set vt : Vec ℝ E.k := fun j => ∑ i, toReal (E.G i j) * toReal (c i) with hvt
  have hvt₁ : ∀ j, toRealVec v j ≤ vt j := fun j => by
    simp only [toRealVec, hvt, hv j]; exact dotDown_le _ _
  have hvt₂ : ∀ j, vt j - toRealVec v j ≤ toReal (ev j) := fun j => by
    rw [hev j]
    exact le_trans (sub_le_sub_right (le_dotUp (fun i => E.G i j) c) _) (sub_le_subUp _ _)
  -- the exact `δ` and its rounding gap
  set δt := toReal y - ∑ i, toReal (c i) * toReal (E.c i) with hδt
  have hδ₁ : toReal (subDown y (dotUp c E.c)) ≤ δt :=
    le_trans (subDown_le_sub _ _) (sub_le_sub_left (le_dotUp c E.c) _)
  have hδ₂ : δt - toReal (subDown y (dotUp c E.c))
      ≤ toReal (subUp (subUp y (dotDown c E.c)) (subDown y (dotUp c E.c))) := le_trans
    (sub_le_sub_right (le_trans (sub_le_sub_left (dotDown_le c E.c) _) (sub_le_subUp _ _)) _)
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
  -- the gap of `v` through `u`, whose entries are in `[-1, 1]`
  have hev : |∑ j, (vt j - toRealVec v j) * u j| ≤ toReal (sumUp ev) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (sum_le_sumUp _))
    refine Finset.sum_le_sum fun j _ => ?_
    have h0 : 0 ≤ vt j - toRealVec v j := sub_nonneg.mpr (hvt₁ j)
    rw [abs_mul, abs_of_nonneg h0]
    have hu1 : |u j| ≤ 1 := le_trans (abs_le_norm₂ u j) hu
    calc (vt j - toRealVec v j) * |u j| ≤ (vt j - toRealVec v j) * 1 :=
          mul_le_mul_of_nonneg_left hu1 h0
      _ ≤ toReal (ev j) := by rw [mul_one]; exact hvt₂ j
  -- `vᵀ u - δ = (c x - y) - c e - (vt - v)ᵀ u + (δt - δ)`
  have hsw : ∑ i, toReal (c i) * ∑ j, toReal (E.G i j) * u j = ∑ j, vt j * u j := by
    simp only [hvt, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hcx : ∑ i, toReal (c i) * (toReal (E.c i) + ∑ j, toReal (E.G i j) * u j + e i)
      - toReal y = (∑ j, vt j * u j) - δt + ce := by
    simp only [mul_add, Finset.sum_add_distrib, hsw, hδt, hce]
    ring
  have hsplit : toRealVec v ⬝ᵥ u - toReal (subDown y (dotUp c E.c))
      = (∑ i, toReal (c i) * (toReal (E.c i) + ∑ j, toReal (E.G i j) * u j + e i) - toReal y)
        - ce - ∑ j, (vt j - toRealVec v j) * u j + (δt - toReal (subDown y (dotUp c E.c))) := by
    rw [hcx]
    simp only [dotProduct, sub_mul, Finset.sum_sub_distrib]
    ring
  -- `φ'` is above the three widenings, and each part is bounded
  have hφ₁ := add_le_addUp φ box
  have hφ₂ := add_le_addUp (addUp φ box) (sumUp ev)
  have hφ₃ := add_le_addUp (addUp (addUp φ box) (sumUp ev))
    (subUp (subUp y (dotDown c E.c)) δs)
  rw [hsplit, abs_le]
  have a1 := abs_le.mp hx
  have a2 := abs_le.mp hce₁
  have a3 := abs_le.mp hev
  constructor <;> linarith

/-- `λ`, `ν = vᵀ v`, `s = 1 - λ + λ ν` and `sigma_sq` against their directed roundings. -/
theorem Ellipsoid.aux_strip_scalars {k : ℕ} (v : Vec 𝕋 k) {lam δ φ' om omHi νLo νHi sLo sHi corr
    S : 𝕋} (hl0 : 0 ≤ toReal lam) (hom : 0 < toReal om) (h_om : om = subDown FloatOps.one lam)
    (h_omHi : omHi = subUp FloatOps.one lam)
    (h_νLo : νLo = maximum FloatOps.zero (dotDown v v))
    (h_νHi : νHi = sqSumUp fun j => absolute (v j))
    (h_sLo : sLo = maximum om (addDown om (mulDown lam νLo)))
    (h_sHi : sHi = addUp omHi (mulUp lam νHi))
    (h_corr : corr = divDown (mulDown (maximum FloatOps.zero (mulDown lam om))
      (maximum FloatOps.zero (mulDown δ δ))) sHi)
    (h_S : S = subUp (addUp omHi (mulUp lam (mulUp φ' φ'))) corr) :
    toReal om ≤ 1 - toReal lam ∧ toRealVec v ⬝ᵥ toRealVec v ≤ toReal νHi
      ∧ 0 < toReal sLo ∧ toReal sLo ≤ 1 - toReal lam + toReal lam * (toRealVec v ⬝ᵥ toRealVec v)
      ∧ 1 - toReal lam + toReal lam * (toRealVec v ⬝ᵥ toRealVec v) ≤ toReal sHi
      ∧ 1 - toReal lam + toReal lam * toReal φ' ^ 2 - toReal lam * (1 - toReal lam)
          * toReal δ ^ 2 / (1 - toReal lam + toReal lam * (toRealVec v ⬝ᵥ toRealVec v))
        ≤ toReal S := by -- --- PROOF ---
  set l := toReal lam with hl
  set ν := toRealVec v ⬝ᵥ toRealVec v with hν
  have hν0 : 0 ≤ ν := by rw [hν, dotProduct_self]; positivity
  have hom₁ : toReal om ≤ 1 - l := by
    have := subDown_le_sub FloatOps.one lam; rwa [toReal_one, ← h_om] at this
  have hom₂ : 1 - l ≤ toReal omHi := by
    have := sub_le_subUp FloatOps.one lam; rwa [toReal_one, ← h_omHi] at this
  -- `ν` between its roundings
  have hνHi : ν ≤ toReal νHi := by
    have h := sq_sum_le_sqSumUp (v := toRealVec v) (m := fun j => absolute (v j))
      fun j => by rw [toReal_absolute]; rfl
    rw [hν, dotProduct_self, norm₂_sq, h_νHi]
    exact h
  have hνLo : toReal νLo ≤ ν := by
    rw [h_νLo, toReal_maximum, toReal_zero]
    exact max_le hν0 (dotDown_le v v)
  have hνLo0 : 0 ≤ toReal νLo := by
    rw [h_νLo, toReal_maximum, toReal_zero]; exact le_max_left _ _
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
  refine ⟨hom₁, hνHi, hsLo₀, hsLo, hsHi, ?_⟩
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
    (hgγ : toReal g ≤ toReal γLo) :
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

/-- The factored point through `G`: `G (κ v + a w + b (vᵀ w) v) = κ G v + (a G + b (G v) vᵀ) w`,
row by row. -/
theorem Ellipsoid.aux_strip_row {k : ℕ} (G : Mat ℝ n k) {v w u : Vec ℝ k} {κ a b : ℝ}
    (h : u = κ • v + a • w + (b * (v ⬝ᵥ w)) • v) (i : Fin n) :
    ∑ j, G i j * u j = κ * (∑ j, G i j * v j)
      + ∑ j, (a * G i j + b * (∑ l, G i l * v l) * v j) * w j := by -- --- PROOF ---
  subst h
  have e1 : ∑ j, G i j * ((b * (v ⬝ᵥ w)) * v j) = (b * (v ⬝ᵥ w)) * ∑ j, G i j * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, (b * (∑ l, G i l * v l) * v j) * w j
      = (b * (∑ l, G i l * v l)) * (v ⬝ᵥ w) := by
    rw [dotProduct, Finset.mul_sum _ (fun j => v j * w j)]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ j, G i j * (κ * v j) = κ * ∑ j, G i j * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e4 : ∑ j, G i j * (a * w j) = ∑ j, a * G i j * w j :=
    Finset.sum_congr rfl fun j _ => by ring
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, add_mul]
  rw [e1, e2, e3, e4]
  ring

/-- One stored generator entry `α G + β (G v) v`, against its two roundings. -/
theorem Ellipsoid.aux_strip_gen {α β Gij vj wLo wHi : 𝕋} {W : ℝ} (hW₁ : toReal wLo ≤ W)
    (hW₂ : W ≤ toReal wHi) :
    let lo := Interval.mulLo (Interval.mulLo β β wLo wHi) (Interval.mulHi β β wLo wHi) vj vj
    let hi := Interval.mulHi (Interval.mulLo β β wLo wHi) (Interval.mulHi β β wLo wHi) vj vj
    |toReal α * toReal Gij + toReal β * W * toReal vj - toReal (addDown (mulDown α Gij) lo)|
      ≤ toReal (subUp (addUp (mulUp α Gij) hi) (addDown (mulDown α Gij) lo)) := by -- --- PROOF ---
  intro lo hi
  have hb := Ellipsoid.aux_mul_mem_corners (le_refl (toReal β)) (le_refl _) hW₁ hW₂
  have hc := Ellipsoid.aux_mul_mem_corners (x := toReal vj) hb.1 hb.2 (le_refl _) (le_refl _)
  have m1 := mulDown_le_mul α Gij
  have m2 := mul_le_mulUp α Gij
  have a1 := addDown_le_add (mulDown α Gij) lo
  have a2 := add_le_addUp (mulUp α Gij) hi
  have s1 := sub_le_subUp (addUp (mulUp α Gij) hi) (addDown (mulDown α Gij) lo)
  rw [abs_le]
  constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.intersectStripGollamudi_outer (steps : ℕ) (E : Ellipsoid 𝕋 n) (c : Vec 𝕋 n)
    (φ y lam : 𝕋) :
    E.construct ∩ {x | |∑ i, toReal (c i) * x i - toReal y| ≤ toReal φ}
      ⊆ (Ellipsoid.intersectStripGollamudi steps E c φ y lam).construct := by -- --- PROOF ---
  rintro x ⟨hxE, hxS⟩
  unfold Ellipsoid.intersectStripGollamudi
  extract_lets vV v ev δ eδ mag φ' νLo νHi om omHi sLo sHi corr S α g β γLo aLo aHi κLo κHi
    wLoV wHiV wLo wHi qLo qHi bLo bHi GLo GHi GD
  split_ifs with hc
  swap
  · exact hxE
  obtain ⟨hl0, hom, hγLo, hgγ⟩ := hc
  rw [Ellipsoid.materialise_eq]
  -- the four checks, read as reals
  have hl0' : 0 ≤ toReal lam := by
    have := toReal_le_of_le hl0; rwa [toReal_zero] at this
  have hom' : 0 < toReal om := by
    have := toReal_lt_of_ltStrict hom; rwa [toReal_zero] at this
  have hγLo' : 0 < toReal γLo := by
    have := toReal_lt_of_ltStrict hγLo; rwa [toReal_zero] at this
  -- the point: `x = E.c + G u + e`
  obtain ⟨xn, hxn, e, he, rfl⟩ := hxE
  obtain ⟨u, hu, hxu⟩ := Ellipsoid.mem_nominalSet_iff.mp hxn
  have he' : ∀ i, toReal (E.I_error.inf i) ≤ e i ∧ e i ≤ toReal (E.I_error.sup i) := fun i => he i
  have hxS' : |∑ i, toReal (c i) * (toReal (E.c i) + ∑ j, toReal (E.G i j) * u j + e i)
      - toReal y| ≤ toReal φ := by
    have h : |∑ i, toReal (c i) * (xn + e) i - toReal y| ≤ toReal φ := hxS
    simpa only [Pi.add_apply, hxu] using h
  -- the strip in the factor vector, and the scalars
  have hstrip := Ellipsoid.aux_strip_widen E c φ y hu he' hxS'
    (v := v) (ev := ev) (fun j => by simp [v, vV]) (fun _ => rfl)
  obtain ⟨hom₁, hνHi, hsLo₀, hsLo, hsHi, hσ⟩ := Ellipsoid.aux_strip_scalars v (δ := δ)
    (φ' := φ') hl0' hom' rfl rfl rfl rfl rfl rfl rfl rfl
  have hν0 : 0 ≤ toRealVec v ⬝ᵥ toRealVec v := by rw [dotProduct_self]; positivity
  have hβ : toReal β ≤ 0 := by
    simp only [β]
    split_ifs
    · rw [toReal_minimum, toReal_zero]; exact min_le_left _ _
    · rw [toReal_zero]
  obtain ⟨hα, hγ, hSα, hSγ⟩ := Ellipsoid.aux_strip_factor (S := S) steps hom' hom₁ hν0 hνHi
    hsLo₀ hsLo rfl rfl hβ rfl hγLo' (toReal_le_of_le hgγ)
  obtain ⟨w, hw, huw⟩ := Ellipsoid.exists_ball_of_strip (v := toRealVec v) (u := u) hl0'
    (by linarith) hu hstrip hσ hα hγ hSα hSγ
  -- `κ = λ δ / s` and `G v`, between their roundings
  set κ := toReal lam * toReal δ / (1 - toReal lam + toReal lam * (toRealVec v ⬝ᵥ toRealVec v))
    with hκ
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
  set W : Vec ℝ n := fun i => ∑ j, toReal (E.G i j) * toRealVec v j with hW
  have hW₁ : ∀ i, toReal (wLo i) ≤ W i ∧ W i ≤ toReal (wHi i) := fun i => by
    simp only [wLo, wHi, wLoV, wHiV, Vector.getElem_ofFn]
    exact ⟨dotDown_le _ _, le_dotUp _ _⟩
  -- the exact generators `α G + β (G v) vᵀ`
  set Gt : Mat ℝ n E.k := fun i j => toReal α * toReal (E.G i j) + toReal β * W i * toRealVec v j
    with hGt
  have hGt₁ : ∀ i j, |Gt i j - toReal (GLo i j)| ≤ toReal (GD i j) := fun i j =>
    Ellipsoid.aux_strip_gen (hW₁ i).1 (hW₁ i).2
  -- the point, as the new nominal point plus the three remainders
  refine ⟨fun i => toReal (qLo i) + ∑ j, toReal (GLo i j) * w j,
    Ellipsoid.mem_nominalSet_iff.mpr ⟨w, hw, fun _ => rfl⟩,
    fun i => (e i + ((toReal (E.c i) + κ * W i) - toReal (qLo i)))
      + ∑ j, (Gt i j - toReal (GLo i j)) * w j,
    Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨e, he, _,
      Interval.sub_mem_residual (x := fun i => toReal (E.c i) + κ * W i) (fun i => ?_), rfl⟩,
      _, Ellipsoid.mem_generatorError hGt₁ hw, rfl⟩, ?_⟩
  · have hm := Ellipsoid.aux_mul_mem_corners hκ₁.1 hκ₁.2 (hW₁ i).1 (hW₁ i).2
    have a1 := addDown_le_add (E.c i) (Interval.mulLo κLo κHi (wLo i) (wHi i))
    have a2 := add_le_addUp (E.c i) (Interval.mulHi κLo κHi (wLo i) (wHi i))
    exact ⟨by simp only [qLo]; linarith, by simp only [qHi]; linarith⟩
  · funext i
    have hrow := Ellipsoid.aux_strip_row (fun i j => toReal (E.G i j)) huw i
    simp only [Pi.add_apply, hxu, Finset.sum_sub_distrib, sub_mul]
    rw [hrow]
    simp only [hGt, hW]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

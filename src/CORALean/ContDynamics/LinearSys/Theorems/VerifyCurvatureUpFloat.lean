module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyCurvatureUpFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsDotProductLeWeightedSum
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `LinearSys.verifyCurvatureUpFloat` bounds the curvature term along the exact direction

For every matrix `F` within `F_r` of `F_c` entry by entry and every point `x = c + G b` of the
initial set: `ℓ F x = ℓ̃ F_c x + ℓ̃ (F − F_c) x + (ℓ − ℓ̃) F x`. The first part is
`ℓ̃'(F_c c) + Σⱼ (ℓ̃'(F_c gⱼ)) bⱼ`, each product between the corners of its box; the second is at
most `|ℓ̃|'(F_r v)` as every `|xₖ| ≤ vₖ`; the third at most `E βF` as every
`|(F x)ᵢ| ≤ Σₖ (|F_c| + F_r)ᵢₖ vₖ ≤ βF sᵢ` (`MatExp.abs_dotProduct_le_weightedSum`).

## Inputs
* `Fc` – float center of the correction matrix
* `Fr` – float radius of the correction matrix
* `c` – float center
* `G` – float generators
* `v` – float bound of the initial set's magnitudes
* `s` – float scales
* `wr` – float bound of `F_r v`
* `wc` – box of `F_c c`
* `WG` – box of `F_c G`
* `βF` – float scaled bound of `|F| v`
* `ℓ` – float direction
* `E` – float error of the direction
* `ℓr` – exact direction
* `F` – exact matrix
* `b` – factors of the point

## Hypotheses
* `hwc` – the box holds `F_c c`
* `hWG` – the box holds `F_c G`
* `hv` – `v` bounds `|c| + Σⱼ |gⱼ|`
* `hwr` – `wr` bounds `F_r v`
* `hβF0` – `βF` is nonnegative
* `hβF` – `βF` bounds every `Σₖ (|F_c| + F_r)ᵢₖ vₖ / sᵢ`
* `hE` – the weighted error of `ℓ̃` is at most `E`
* `hF` – `F` is within `F_r` of `F_c`
* `hb` – the factors lie in `[-1, 1]`

## Conclusion
* `ℓ (F (c + G b))` is at most the float bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A product with a number between two floats is at most the larger corner, rounded up. -/
private theorem LinearSys.aux_mul_le_max {a lo hi : 𝕋} {y : ℝ} (h1 : toReal lo ≤ y)
    (h2 : y ≤ toReal hi) : -- --- CONCL ---
    toReal a * y ≤ toReal (maximum (mulUp a lo) (mulUp a hi)) := by -- --- PROOF ---
  rw [toReal_maximum]
  rcases le_total 0 (toReal a) with ha | ha
  · exact le_trans (mul_le_mul_of_nonneg_left h2 ha) (le_trans (mul_le_mulUp a hi)
      (le_max_right _ _))
  · exact le_trans (mul_le_mul_of_nonpos_left h1 ha) (le_trans (mul_le_mulUp a lo)
      (le_max_left _ _))

/-- And at least the smaller corner, rounded down. -/
private theorem LinearSys.aux_min_le_mul {a lo hi : 𝕋} {y : ℝ} (h1 : toReal lo ≤ y)
    (h2 : y ≤ toReal hi) : -- --- CONCL ---
    toReal (minimum (mulDown a lo) (mulDown a hi)) ≤ toReal a * y := by -- --- PROOF ---
  rw [toReal_minimum]
  rcases le_total 0 (toReal a) with ha | ha
  · exact le_trans (min_le_left _ _) (le_trans (mulDown_le_mul a lo)
      (mul_le_mul_of_nonneg_left h1 ha))
  · exact le_trans (min_le_right _ _) (le_trans (mulDown_le_mul a hi)
      (mul_le_mul_of_nonpos_left h2 ha))


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.dotProduct_le_verifyCurvatureUpFloat {Fc Fr : Mat 𝕋 n n} (c : Vec 𝕋 n)
    (G : Mat 𝕋 n m) {v s wr : Vec 𝕋 n} {wc : Interval (Vec 𝕋 n)} {WG : Interval (Mat 𝕋 n m)}
    {βF : 𝕋} (hwc : toRealMat Fc *ᵥ toRealVec c ∈ wc.toSet)
    (hWG : toRealMat Fc * toRealMat G ∈ WG.toSet)
    (hv : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal (v i))
    (hwr : ∀ i, ∑ k, toReal (Fr i k) * toReal (v k) ≤ toReal (wr i)) (hβF0 : 0 ≤ toReal βF)
    (hβF : ∀ i, ∑ k, (|toReal (Fc i k)| + toReal (Fr i k)) * toReal (v k)
      ≤ toReal βF * toReal (s i))
    (ℓ : Vec 𝕋 n) {E : 𝕋} {ℓr : Vec ℝ n}
    (hE : ∑ i, |ℓr i - toReal (ℓ i)| * toReal (s i) ≤ toReal E) {F : Mat ℝ n n}
    (hF : ∀ i k, |F i k - toReal (Fc i k)| ≤ toReal (Fr i k)) {b : Fin m → ℝ}
    (hb : ∀ j, |b j| ≤ 1) : -- --- CONCL ---
    ℓr ⬝ᵥ (F *ᵥ (toRealVec c + toRealMat G *ᵥ b))
      ≤ toReal (LinearSys.verifyCurvatureUpFloat wc WG wr βF ℓ E) := by -- --- PROOF ---
  set x := toRealVec c + toRealMat G *ᵥ b with hx
  set e : Vec ℝ n := ℓr - toRealVec ℓ with he
  set Fcr := toRealMat Fc
  have hFr0 : ∀ i k, 0 ≤ toReal (Fr i k) := fun i k => le_trans (abs_nonneg _) (hF i k)
  -- `|xₖ| ≤ vₖ`
  have hxk : ∀ k, |x k| ≤ toReal (v k) := by
    intro k
    refine le_trans ?_ (hv k)
    have hGb : |(toRealMat G *ᵥ b) k| ≤ ∑ j, |toReal (G k j)| := by
      show |∑ j, toRealMat G k j * b j| ≤ _
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hb j)
    simp only [hx, Pi.add_apply, toRealVec]
    exact le_trans (abs_add_le _ _) (add_le_add le_rfl hGb)
  -- the three parts of `ℓ F x`
  have hsplit : ℓr ⬝ᵥ (F *ᵥ x) = toRealVec ℓ ⬝ᵥ (Fcr *ᵥ x) + toRealVec ℓ ⬝ᵥ ((F - Fcr) *ᵥ x)
      + e ⬝ᵥ (F *ᵥ x) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, he, sub_dotProduct]; ring
  -- part 1: `ℓ̃'(F_c c) + Σⱼ (ℓ̃'(F_c gⱼ)) bⱼ`
  set t₁ := sumUp fun i => maximum (mulUp (ℓ i) (wc.inf i)) (mulUp (ℓ i) (wc.sup i))
  set gUp := fun j => sumUp fun i => maximum (mulUp (ℓ i) (WG.inf i j)) (mulUp (ℓ i) (WG.sup i j))
  set gDn := fun j => sumDown fun i =>
    minimum (mulDown (ℓ i) (WG.inf i j)) (mulDown (ℓ i) (WG.sup i j))
  set t₂ := sumUp fun j => maximum (absolute (gUp j)) (absolute (gDn j))
  set t₃ := sumUp fun i => mulUp (absolute (ℓ i)) (wr i)
  have h1 : toRealVec ℓ ⬝ᵥ (Fcr *ᵥ x) ≤ toReal t₁ + toReal t₂ := by
    have hdot : toRealVec ℓ ⬝ᵥ (Fcr *ᵥ x) = toRealVec ℓ ⬝ᵥ (Fcr *ᵥ toRealVec c)
        + ∑ j, (∑ i, toReal (ℓ i) * (Fcr * toRealMat G) i j) * b j := by
      rw [hx, Matrix.mulVec_add, dotProduct_add, Matrix.mulVec_mulVec]
      congr 1
      rw [dotProduct_mulVec]
      rfl
    -- the center's term and each generator's, between the corners of the boxes
    rw [hdot]
    refine add_le_add ?_ ?_
    · refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
      obtain ⟨hlo, hhi⟩ := hwc i
      exact LinearSys.aux_mul_le_max hlo hhi
    · refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
      have hbounds : toReal (gDn j) ≤ ∑ i, toReal (ℓ i) * (Fcr * toRealMat G) i j
          ∧ ∑ i, toReal (ℓ i) * (Fcr * toRealMat G) i j ≤ toReal (gUp j) := by
        refine ⟨le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun i _ => ?_),
          le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)⟩
        · obtain ⟨hlo, hhi⟩ := (Interval.mem_mat_iff.mp hWG) i j
          exact LinearSys.aux_min_le_mul hlo hhi
        · obtain ⟨hlo, hhi⟩ := (Interval.mem_mat_iff.mp hWG) i j
          exact LinearSys.aux_mul_le_max hlo hhi
      rw [toReal_maximum, toReal_absolute, toReal_absolute, max_comm]
      refine le_trans (le_abs_self _) ?_
      rw [abs_mul]
      exact le_trans (mul_le_of_le_one_right (abs_nonneg _) (hb j))
        (abs_le_max_abs_abs hbounds.1 hbounds.2)
  -- part 2: `|ℓ̃|'(F_r v)`
  have h2 : toRealVec ℓ ⬝ᵥ ((F - Fcr) *ᵥ x) ≤ toReal t₃ := by
    refine le_trans (le_abs_self _) (le_trans (Finset.abs_sum_le_sum_abs _ _) ?_)
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
    rw [abs_mul]
    refine le_trans ?_ (mul_le_mulUp _ _)
    rw [toReal_absolute]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    show |∑ k, (F - Fcr) i k * x k| ≤ _
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun k _ => ?_)
      (hwr i))
    rw [abs_mul]
    exact mul_le_mul (hF i k) (hxk k) (abs_nonneg _) (hFr0 i k)
  -- part 3: `E βF`
  have h3 : e ⬝ᵥ (F *ᵥ x) ≤ toReal (mulUp E βF) := by
    have hFx : ∀ i, |(F *ᵥ x) i| ≤ toReal βF * toReal (s i) := by
      intro i
      refine le_trans ?_ (hβF i)
      show |∑ k, F i k * x k| ≤ _
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      -- `|F| ≤ |F_c| + F_r` entry by entry
      have hFik : |F i k| ≤ |toReal (Fc i k)| + toReal (Fr i k) := by
        have := abs_sub_abs_le_abs_sub (F i k) (toReal (Fc i k))
        linarith [hF i k]
      exact mul_le_mul hFik (hxk k) (abs_nonneg _)
        (add_nonneg (abs_nonneg _) (hFr0 i k))
    have h := Real.MatExp.abs_dotProduct_le_weightedSum e (F *ᵥ x) (toRealVec s) hFx
    simp only [he, Pi.sub_apply, toRealVec] at h
    refine le_trans (le_abs_self _) (le_trans h (le_trans ?_ (mul_le_mulUp _ _)))
    exact mul_le_mul_of_nonneg_right hE hβF0
  -- the three parts, added up and rounded up
  rw [hsplit]
  unfold LinearSys.verifyCurvatureUpFloat
  have ha1 := add_le_addUp t₁ t₂
  have ha2 := add_le_addUp (addUp t₁ t₂) t₃
  have ha3 := add_le_addUp (addUp (addUp t₁ t₂) t₃) (mulUp E βF)
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

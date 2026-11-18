module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyInputInnerFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsDotProductLeWeightedSum
public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `LinearSys.verifyInputInnerFloat` bounds the support of one step's held input from below

For `PG` within `ρ_l` (row `l`, summed over the columns) of a member `x` of the box `Vs`, and
`ℓ = ℓ̃ + e` with `Σ_l |e_l| s_l ≤ E`: `|ℓ' PG_c| ≥ |ℓ̃' x_c| − |ℓ̃' (PG − x)_c| − |e' PG_c|`,
`|ℓ̃' x_c|` at least the mignitude of the column's sums rounded down and up, the second summed to
at most `|ℓ̃|'ρ`, the third to at most `E β` once `β s_l` bounds the row sums of `|PG|`.

## Inputs
* `Vs` – float box of the sum of the orders
* `ρ` – float bound of the remainder per row
* `β` – float bound of the scaled row sums
* `s` – positive scales
* `PG` – exact matrix
* `ℓ` – float direction
* `E` – float bound of the direction's weighted error
* `ℓr` – exact direction
* `x` – member of the box

## Hypotheses
* `hβ0` – `β` nonnegative
* `hβ` – `β` bounds the scaled row sums of `|PG|`
* `hE` – the weighted error of the direction is at most `E`
* `hx` – `x` lies in the box
* `hR` – `PG` is within `ρ` of `x`, row by row

## Conclusion
* the float bound is at most `Σ_c |ℓr' PG_c|`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A product with a number between two floats is at most the larger corner, rounded up. -/
private theorem LinearSys.aux_mul_le_max'' {a lo hi : 𝕋} {y : ℝ} (h1 : toReal lo ≤ y)
    (h2 : y ≤ toReal hi) : -- --- CONCL ---
    toReal a * y ≤ toReal (maximum (mulUp a lo) (mulUp a hi)) := by -- --- PROOF ---
  rw [toReal_maximum]
  rcases le_total 0 (toReal a) with ha | ha
  · exact le_trans (mul_le_mul_of_nonneg_left h2 ha) (le_trans (mul_le_mulUp a hi)
      (le_max_right _ _))
  · exact le_trans (mul_le_mul_of_nonpos_left h1 ha) (le_trans (mul_le_mulUp a lo)
      (le_max_left _ _))

/-- And at least the smaller corner, rounded down. -/
private theorem LinearSys.aux_min_le_mul'' {a lo hi : 𝕋} {y : ℝ} (h1 : toReal lo ≤ y)
    (h2 : y ≤ toReal hi) : -- --- CONCL ---
    toReal (minimum (mulDown a lo) (mulDown a hi)) ≤ toReal a * y := by -- --- PROOF ---
  rw [toReal_minimum]
  rcases le_total 0 (toReal a) with ha | ha
  · exact le_trans (min_le_left _ _) (le_trans (mulDown_le_mul a lo)
      (mul_le_mul_of_nonneg_left h1 ha))
  · exact le_trans (min_le_right _ _) (le_trans (mulDown_le_mul a hi)
      (mul_le_mul_of_nonpos_left h2 ha))


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifyInputInnerFloat_le {Vs : Interval (Mat 𝕋 n m)} {ρ : Vec 𝕋 n} {β : 𝕋}
    {s : Vec 𝕋 n} (hβ0 : 0 ≤ toReal β) {PG : Mat ℝ n m}
    (hβ : ∀ l, ∑ c, |PG l c| ≤ toReal β * toReal (s l)) (ℓ : Vec 𝕋 n) {E : 𝕋} {ℓr : Vec ℝ n}
    (hE : ∑ l, |ℓr l - toReal (ℓ l)| * toReal (s l) ≤ toReal E) {x : Mat ℝ n m}
    (hx : x ∈ Vs.toSet) (hR : ∀ l, ∑ c, |PG l c - x l c| ≤ toReal (ρ l)) : -- --- CONCL ---
    toReal (LinearSys.verifyInputInnerFloat Vs ρ β ℓ E)
      ≤ ∑ c, |ℓr ⬝ᵥ (fun l => PG l c)| := by -- --- PROOF ---
  have hmem := Interval.mem_mat_iff.mp hx
  set e : Vec ℝ n := ℓr - toRealVec ℓ with he
  set mig := fun c =>
    let up := sumUp fun l => maximum (mulUp (ℓ l) (Vs.inf l c)) (mulUp (ℓ l) (Vs.sup l c))
    let dn := sumDown fun l => minimum (mulDown (ℓ l) (Vs.inf l c)) (mulDown (ℓ l) (Vs.sup l c))
    maximum FloatOps.zero (maximum dn (neg up)) with hmig
  set t₂ := sumUp fun l => mulUp (absolute (ℓ l)) (ρ l)
  -- each column: `|ℓ̃' x_c|` from below, the remainder and the error from above
  have hcol : ∀ c, toReal (mig c) - ∑ l, |toReal (ℓ l)| * |PG l c - x l c|
      - ∑ l, |e l| * |PG l c| ≤ |ℓr ⬝ᵥ (fun l => PG l c)| := by
    intro c
    have hup : ∑ l, toReal (ℓ l) * x l c ≤ toReal (sumUp fun l =>
        maximum (mulUp (ℓ l) (Vs.inf l c)) (mulUp (ℓ l) (Vs.sup l c))) :=
      le_trans (Finset.sum_le_sum fun l _ => LinearSys.aux_mul_le_max'' (hmem l c).1
        (hmem l c).2) (sum_le_sumUp _)
    have hdn : toReal (sumDown fun l =>
        minimum (mulDown (ℓ l) (Vs.inf l c)) (mulDown (ℓ l) (Vs.sup l c)))
        ≤ ∑ l, toReal (ℓ l) * x l c :=
      le_trans (sumDown_le_sum _)
        (Finset.sum_le_sum fun l _ => LinearSys.aux_min_le_mul'' (hmem l c).1 (hmem l c).2)
    have hm : toReal (mig c) ≤ |∑ l, toReal (ℓ l) * x l c| := by
      simp only [hmig, toReal_maximum, toReal_neg]
      refine max_le (by rw [toReal_zero]; exact abs_nonneg _) (max_le ?_ ?_)
      · exact le_trans hdn (le_abs_self _)
      · exact le_trans (neg_le_neg hup) (neg_le_abs _)
    -- `ℓr' PG_c = ℓ̃' x_c + ℓ̃' (PG − x)_c + e' PG_c`
    have hsplit : ℓr ⬝ᵥ (fun l => PG l c) = ∑ l, toReal (ℓ l) * x l c
        + ∑ l, toReal (ℓ l) * (PG l c - x l c) + ∑ l, e l * PG l c := by
      simp only [dotProduct, he, Pi.sub_apply, toRealVec, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    -- the remainder's and the error's parts, each bounded by its absolute terms
    have hr1 : |∑ l, toReal (ℓ l) * (PG l c - x l c)| ≤ ∑ l, |toReal (ℓ l)| * |PG l c - x l c| :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq (by simp [abs_mul]))
    have hr2 : |∑ l, e l * PG l c| ≤ ∑ l, |e l| * |PG l c| :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq (by simp [abs_mul]))
    rw [hsplit]
    have := abs_add_le (∑ l, toReal (ℓ l) * x l c + ∑ l, toReal (ℓ l) * (PG l c - x l c)
      + ∑ l, e l * PG l c) (-(∑ l, toReal (ℓ l) * (PG l c - x l c)) - ∑ l, e l * PG l c)
    have h4 := abs_add_le (-(∑ l, toReal (ℓ l) * (PG l c - x l c))) (-(∑ l, e l * PG l c))
    simp only [abs_neg] at h4
    have h5 : ∑ l, toReal (ℓ l) * x l c + ∑ l, toReal (ℓ l) * (PG l c - x l c)
        + ∑ l, e l * PG l c + (-(∑ l, toReal (ℓ l) * (PG l c - x l c)) - ∑ l, e l * PG l c)
        = ∑ l, toReal (ℓ l) * x l c := by ring
    rw [h5] at this
    have h6 : |-(∑ l, toReal (ℓ l) * (PG l c - x l c)) - ∑ l, e l * PG l c|
        ≤ |∑ l, toReal (ℓ l) * (PG l c - x l c)| + |∑ l, e l * PG l c| := by
      rw [sub_eq_add_neg]; simpa using h4
    linarith
  -- summed over the columns: the remainder within `t₂`, the error within `E β`
  have hrem : ∑ c, ∑ l, |toReal (ℓ l)| * |PG l c - x l c| ≤ toReal t₂ := by
    rw [Finset.sum_comm]
    refine le_trans (Finset.sum_le_sum fun l _ => ?_) (sum_le_sumUp _)
    rw [← Finset.mul_sum]
    refine le_trans ?_ (mul_le_mulUp _ _)
    rw [toReal_absolute]
    exact mul_le_mul_of_nonneg_left (hR l) (abs_nonneg _)
  have herr : ∑ c, ∑ l, |e l| * |PG l c| ≤ toReal (mulUp E β) := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hβ l)
      (abs_nonneg _)) ?_
    have : ∑ l, |e l| * (toReal β * toReal (s l)) = (∑ l, |e l| * toReal (s l)) * toReal β := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [this]
    simp only [he, Pi.sub_apply, toRealVec]
    exact le_trans (mul_le_mul_of_nonneg_right hE hβ0) (mul_le_mulUp _ _)
  -- the column bounds summed, and the float result below them
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hcol c
  simp only [Finset.sum_sub_distrib] at hsum
  unfold LinearSys.verifyInputInnerFloat
  have hd1 := subDown_le_sub (subDown (sumDown mig) t₂) (mulUp E β)
  have hd2 := subDown_le_sub (sumDown mig) t₂
  have hd3 := sumDown_le_sum mig
  dsimp only
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

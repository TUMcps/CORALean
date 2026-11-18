module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyBoxDotDownFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsDotProductLeWeightedSum
public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `LinearSys.verifyBoxDotDownFloat` bounds the dot product with a box from below

For `x` in the box `X` and `ℓ = ℓ̃ + e` with `Σ_l |e_l| s_l ≤ E`: `ℓ̃_l x_lc` is at least the
smaller corner product, rounded down, and `|e' Σ_c x_c| ≤ E β` once `Σ_c |X|_lc ≤ β s_l` for every
row (`Real.MatExp.abs_dotProduct_le_weightedSum`).

## Inputs
* `X` – float box
* `x` – member of the box
* `β` – float bound of the scaled row sums
* `s` – positive scales
* `ℓ` – float direction
* `E` – float bound of the direction's weighted error
* `ℓr` – exact direction

## Hypotheses
* `hx` – `x` lies in the box
* `hβ0` – `β` nonnegative
* `hβ` – `β` bounds the scaled row sums of the box's magnitude
* `hE` – the weighted error of the direction is at most `E`

## Conclusion
* `ℓr' Σ_c x_c` is at least the float bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A product with a number between two floats is at least the smaller corner, rounded down. -/
private theorem LinearSys.aux_min_le_mul' {a lo hi : 𝕋} {y : ℝ} (h1 : toReal lo ≤ y)
    (h2 : y ≤ toReal hi) : -- --- CONCL ---
    toReal (minimum (mulDown a lo) (mulDown a hi)) ≤ toReal a * y := by -- --- PROOF ---
  rw [toReal_minimum]
  rcases le_total 0 (toReal a) with ha | ha
  · exact le_trans (min_le_left _ _) (le_trans (mulDown_le_mul a lo)
      (mul_le_mul_of_nonneg_left h1 ha))
  · exact le_trans (min_le_right _ _) (le_trans (mulDown_le_mul a hi)
      (mul_le_mul_of_nonpos_left h2 ha))


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifyBoxDotDownFloat_le_dotProduct {X : Interval (Mat 𝕋 n k)} {x : Mat ℝ n k}
    (hx : x ∈ X.toSet) {β : 𝕋} {s : Vec 𝕋 n} (hβ0 : 0 ≤ toReal β)
    (hβ : ∀ l, ∑ c, toReal (X.magnitudeMat l c) ≤ toReal β * toReal (s l)) (ℓ : Vec 𝕋 n)
    {E : 𝕋} {ℓr : Vec ℝ n}
    (hE : ∑ l, |ℓr l - toReal (ℓ l)| * toReal (s l) ≤ toReal E) : -- --- CONCL ---
    toReal (LinearSys.verifyBoxDotDownFloat X β ℓ E) ≤ ℓr ⬝ᵥ (fun l => ∑ c, x l c)
        := by -- --- PROOF ---
  have hmem := Interval.mem_mat_iff.mp hx
  set e : Vec ℝ n := ℓr - toRealVec ℓ with he
  have hsplit : ℓr ⬝ᵥ (fun l => ∑ c, x l c)
      = ∑ c, ∑ l, toReal (ℓ l) * x l c + e ⬝ᵥ (fun l => ∑ c, x l c) := by
    have : ℓr = toRealVec ℓ + e := by rw [he]; abel
    rw [this, add_dotProduct]
    congr 1
    simp only [dotProduct, toRealVec, Finset.mul_sum]
    exact Finset.sum_comm
  -- the corners, and the error against the row sums
  have h1 : toReal (sumDown fun c => sumDown fun l =>
      minimum (mulDown (ℓ l) (X.inf l c)) (mulDown (ℓ l) (X.sup l c)))
      ≤ ∑ c, ∑ l, toReal (ℓ l) * x l c := by
    refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun c _ => ?_)
    refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun l _ => ?_)
    exact LinearSys.aux_min_le_mul' (hmem l c).1 (hmem l c).2
  -- the row sums within `β s`, so the error term is at most `E β`
  have hy : ∀ l, |(fun l => ∑ c, x l c) l| ≤ toReal β * toReal (s l) := by
    intro l
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun c _ => ?_)
      (hβ l))
    rw [Interval.magnitudeMat, toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs (hmem l c).1 (hmem l c).2
  have h2 : -toReal (mulUp E β) ≤ e ⬝ᵥ (fun l => ∑ c, x l c) := by
    have h := Real.MatExp.abs_dotProduct_le_weightedSum e _ (toRealVec s) hy
    simp only [he, Pi.sub_apply, toRealVec] at h
    have h' := le_trans h (le_trans (mul_le_mul_of_nonneg_right hE hβ0) (mul_le_mulUp E β))
    linarith [neg_abs_le (e ⬝ᵥ (fun l => ∑ c, x l c))]
  rw [hsplit]
  unfold LinearSys.verifyBoxDotDownFloat
  linarith [subDown_le_sub (sumDown fun c => sumDown fun l =>
    minimum (mulDown (ℓ l) (X.inf l c)) (mulDown (ℓ l) (X.sup l c))) (mulUp E β)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

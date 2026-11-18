module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyInputOuterFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsDotProductLeWeightedSum
public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `LinearSys.verifyInputOuterFloat` bounds the support of one step's varying input

For `z = Σᵢ Xᵢ bᵢ + y` with every `Xᵢ` in the box `Vᵢ`, `|bᵢ| ≤ 1` and `|y_l| ≤ ρ_l`, and
`ℓ = ℓ̃ + e` with `Σ_l |e_l| s_l ≤ E`: `ℓ̃' Xᵢ bᵢ ≤ Σ_c |ℓ̃' Xᵢ_c|`, each between the column's sums
rounded down and up, `ℓ̃' y ≤ |ℓ̃|'ρ`, and `|e' z| ≤ E β` once `β s_l` bounds row `l` of the
magnitudes and the remainder.

## Inputs
* `V` – float boxes of the orders
* `ρ` – float bound of the remainder per row
* `β` – float bound of the scaled row sums
* `s` – positive scales
* `ℓ` – float direction
* `E` – float bound of the direction's weighted error
* `ℓr` – exact direction
* `X` – members of the boxes
* `b` – factors
* `y` – remainder

## Hypotheses
* `hβ0` – `β` nonnegative
* `hβ` – `β` bounds the scaled row sums of the magnitudes and the remainder
* `hE` – the weighted error of the direction is at most `E`
* `hX` – every `Xᵢ` lies in its box
* `hb` – the factors lie in `[-1, 1]`
* `hy` – the remainder is within `ρ`

## Conclusion
* `ℓr' z` is at most the float bound
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

/-- A fold of `addUp` from `a` is at least `a` plus the exact sum. -/
private theorem LinearSys.aux_sum_le_foldl {α : Type} (f : α → 𝕋) : -- --- CONCL ---
    ∀ (V : List α) (a : 𝕋),
      toReal a + (V.map fun X => toReal (f X)).sum
        ≤ toReal (V.foldl (fun acc X => addUp acc (f X)) a) := by -- --- PROOF ---
  intro V
  induction V with
  | nil => intro a; simp
  | cons X V ih =>
    intro a
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    have h := ih (addUp a (f X))
    linarith [add_le_addUp a (f X)]

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

/-- `|ℓ̃' x_c|` for `x` in the box is at most the magnitude of the column's sums. -/
private theorem LinearSys.aux_abs_dot_le {X : Interval (Mat 𝕋 n m)} {x : Mat ℝ n m}
    (hx : x ∈ X.toSet) (ℓ : Vec 𝕋 n) (c : Fin m) : -- --- CONCL ---
    |∑ l, toReal (ℓ l) * x l c| ≤ toReal (LinearSys.step_verifyBoxDotAbsFloat X ℓ
        c) := by -- --- PROOF ---
  have hmem := Interval.mem_mat_iff.mp hx
  have hup : ∑ l, toReal (ℓ l) * x l c ≤ toReal (sumUp fun l =>
      maximum (mulUp (ℓ l) (X.inf l c)) (mulUp (ℓ l) (X.sup l c))) :=
    le_trans (Finset.sum_le_sum fun l _ => LinearSys.aux_mul_le_max'' (hmem l c).1 (hmem l c).2)
      (sum_le_sumUp _)
  have hdn : toReal (sumDown fun l =>
      minimum (mulDown (ℓ l) (X.inf l c)) (mulDown (ℓ l) (X.sup l c)))
      ≤ ∑ l, toReal (ℓ l) * x l c :=
    le_trans (sumDown_le_sum _)
      (Finset.sum_le_sum fun l _ => LinearSys.aux_min_le_mul'' (hmem l c).1 (hmem l c).2)
  unfold LinearSys.step_verifyBoxDotAbsFloat
  rw [toReal_maximum, toReal_absolute, toReal_absolute, max_comm]
  exact abs_le_max_abs_abs hdn hup


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.dotProduct_le_verifyInputOuterFloat {V : List (Interval (Mat 𝕋 n m))}
    {ρ : Vec 𝕋 n} {β : 𝕋} {s : Vec 𝕋 n} (hβ0 : 0 ≤ toReal β)
    (hβ : ∀ l, (V.map fun X => ∑ c, toReal (X.magnitudeMat l c)).sum + toReal (ρ l)
      ≤ toReal β * toReal (s l))
    (ℓ : Vec 𝕋 n) {E : 𝕋} {ℓr : Vec ℝ n}
    (hE : ∑ l, |ℓr l - toReal (ℓ l)| * toReal (s l) ≤ toReal E)
    {X : Fin V.length → Mat ℝ n m} (hX : ∀ i, X i ∈ (V[i.1]).toSet)
    {b : Fin V.length → Fin m → ℝ} (hb : ∀ i c, |b i c| ≤ 1) {y : Vec ℝ n}
    (hy : ∀ l, |y l| ≤ toReal (ρ l)) : -- --- CONCL ---
    ℓr ⬝ᵥ ((∑ i, X i *ᵥ b i) + y) ≤ toReal (LinearSys.verifyInputOuterFloat V ρ β
        ℓ E) := by -- --- PROOF ---
  set z := (∑ i, X i *ᵥ b i) + y with hz
  set e : Vec ℝ n := ℓr - toRealVec ℓ with he
  set t₁ := V.foldl (fun acc X => addUp acc
    (sumUp fun c => LinearSys.step_verifyBoxDotAbsFloat X ℓ c)) zero
  set t₂ := sumUp fun l => mulUp (absolute (ℓ l)) (ρ l)
  have hsplit : ℓr ⬝ᵥ z = ∑ i, toRealVec ℓ ⬝ᵥ (X i *ᵥ b i) + toRealVec ℓ ⬝ᵥ y + e ⬝ᵥ z := by
    have : ℓr = toRealVec ℓ + e := by rw [he]; abel
    rw [this, add_dotProduct, hz, dotProduct_add, dotProduct_sum]
  -- the orders: each column's `|ℓ̃' Xᵢ_c|`
  have h1 : ∑ i, toRealVec ℓ ⬝ᵥ (X i *ᵥ b i) ≤ toReal t₁ := by
    have hi : ∀ i, toRealVec ℓ ⬝ᵥ (X i *ᵥ b i)
        ≤ toReal (sumUp fun c => LinearSys.step_verifyBoxDotAbsFloat V[i.1] ℓ c) := by
      intro i
      rw [dotProduct_mulVec]
      refine le_trans (Finset.sum_le_sum fun c _ => ?_) (sum_le_sumUp _)
      show (∑ l, toReal (ℓ l) * X i l c) * b i c ≤ _
      refine le_trans (le_abs_self _) ?_
      rw [abs_mul]
      exact le_trans (mul_le_of_le_one_right (abs_nonneg _) (hb i c))
        (LinearSys.aux_abs_dot_le (hX i) ℓ c)
    have hfold := LinearSys.aux_sum_le_foldl
      (fun X => sumUp fun c => LinearSys.step_verifyBoxDotAbsFloat X ℓ c) V zero
    rw [toReal_zero, zero_add, ← Fin.sum_univ_fun_getElem] at hfold
    exact le_trans (Finset.sum_le_sum fun i _ => hi i) hfold
  -- the remainder
  have h2 : toRealVec ℓ ⬝ᵥ y ≤ toReal t₂ := by
    refine le_trans (le_abs_self _) (le_trans (Finset.abs_sum_le_sum_abs _ _) ?_)
    refine le_trans (Finset.sum_le_sum fun l _ => ?_) (sum_le_sumUp _)
    rw [abs_mul]
    refine le_trans ?_ (mul_le_mulUp _ _)
    rw [toReal_absolute]
    exact mul_le_mul_of_nonneg_left (hy l) (abs_nonneg _)
  -- the error, against the row sums of the magnitudes and the remainder
  have hzl : ∀ l, |z l| ≤ toReal β * toReal (s l) := by
    intro l
    refine le_trans ?_ (hβ l)
    rw [← Fin.sum_univ_fun_getElem]
    simp only [hz, Pi.add_apply, Finset.sum_apply]
    refine le_trans (abs_add_le _ _) (add_le_add ?_ (hy l))
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    -- one order's entry, within its box's magnitude
    show |∑ c, X i l c * b i c| ≤ _
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun c _ => ?_)
    rw [abs_mul]
    have hmem := Interval.mem_mat_iff.mp (hX i) l c
    refine le_trans (mul_le_of_le_one_right (abs_nonneg _) (hb i c)) ?_
    rw [Interval.magnitudeMat, toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs hmem.1 hmem.2
  -- the error along the exact row, within `E β`
  have h3 : e ⬝ᵥ z ≤ toReal (mulUp E β) := by
    have h := Real.MatExp.abs_dotProduct_le_weightedSum e z (toRealVec s) hzl
    simp only [he, Pi.sub_apply, toRealVec] at h
    exact le_trans (le_abs_self _) (le_trans h (le_trans
      (mul_le_mul_of_nonneg_right hE hβ0) (mul_le_mulUp _ _)))
  rw [hsplit]
  unfold LinearSys.verifyInputOuterFloat
  linarith [add_le_addUp t₁ t₂, add_le_addUp (addUp t₁ t₂) (mulUp E β)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

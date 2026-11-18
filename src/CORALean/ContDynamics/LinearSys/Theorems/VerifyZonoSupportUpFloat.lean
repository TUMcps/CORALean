module

public import CORALean.ContDynamics.LinearSys.Definitions.Basic
public import CORALean.ContDynamics.LinearSys.Operations.VerifyZonoSupportUpFloat
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `LinearSys.verifyZonoSupportUpFloat` bounds the support from above

For `x = c + Σⱼ βⱼ gⱼ + e` in a `LinearSys.VerifyZono` and `ℓ = ℓ̃ + δ` with `|δᵢ| ≤ wᵢ`:
`ℓ̃'c ≤ dotUp`, `ℓ̃' Σⱼ βⱼ gⱼ ≤ Σⱼ |ℓ̃'gⱼ|` (each between its dot products rounded down and up),
`ℓ̃'e ≤ |ℓ̃|'r` and `δ'x ≤ w'μ` with `|xᵢ| ≤ μᵢ`.

## Inputs
* `Z` – float zonotope with a box
* `x` – point of it
* `ℓ` – float direction
* `w` – float bound of the error of the direction
* `ℓr` – exact direction

## Hypotheses
* `hx` – `x` lies in `Z`
* `hw` – `ℓr` is within `w` of `ℓ` entrywise

## Conclusion
* `ℓr' x` is at most the float bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A left fold of upward additions is at least its seed plus the sum of the terms. -/
private theorem LinearSys.aux_le_foldl_addUp {α : Type} (f : α → 𝕋) : -- --- CONCL ---
    ∀ (L : List α) (a : 𝕋),
      toReal a + (L.map fun x => toReal (f x)).sum
        ≤ toReal (L.foldl (fun acc x => addUp acc (f x)) a) := by -- --- PROOF ---
  intro L
  induction L with
  | nil => intro a; simp
  | cons x L ih =>
    intro a
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    have := ih (addUp a (f x))
    linarith [add_le_addUp a (f x)]

/-- The support of the span along `ℓ` is at most the sum of `|ℓ'g|`. -/
private theorem LinearSys.aux_genSet_dot_le (ℓ : Vec ℝ q) : -- --- CONCL ---
    ∀ (L : List (Vec ℝ q)) {y : Vec ℝ q}, y ∈ LinearSys.verifyZonoGenSet L →
      ℓ ⬝ᵥ y ≤ (L.map fun g => |ℓ ⬝ᵥ g|).sum := by -- --- PROOF ---
  intro L
  induction L with
  | nil =>
    intro y hy
    have hy0 : y = 0 := hy
    simp [hy0]
  | cons g L ih =>
    intro y hy
    obtain ⟨β, hβ, y', hy', rfl⟩ := hy
    simp only [List.map_cons, List.sum_cons, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have h1 : β * (ℓ ⬝ᵥ g) ≤ |ℓ ⬝ᵥ g| := by
      calc β * (ℓ ⬝ᵥ g) ≤ |β * (ℓ ⬝ᵥ g)| := le_abs_self _
        _ = |β| * |ℓ ⬝ᵥ g| := abs_mul _ _
        _ ≤ 1 * |ℓ ⬝ᵥ g| := mul_le_mul_of_nonneg_right hβ (abs_nonneg _)
        _ = |ℓ ⬝ᵥ g| := one_mul _
    linarith [ih hy']

/-- An entry of a point of the span is at most the sum of the entries' magnitudes. -/
private theorem LinearSys.aux_genSet_abs_le (i : Fin q) : -- --- CONCL ---
    ∀ (L : List (Vec ℝ q)) {y : Vec ℝ q}, y ∈ LinearSys.verifyZonoGenSet L →
      |y i| ≤ (L.map fun g => |g i|).sum := by -- --- PROOF ---
  intro L
  induction L with
  | nil =>
    intro y hy
    have hy0 : y = 0 := hy
    simp [hy0]
  | cons g L ih =>
    intro y hy
    obtain ⟨β, hβ, y', hy', rfl⟩ := hy
    simp only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : |β * g i| ≤ |g i| := by
      rw [abs_mul]; exact le_trans (mul_le_mul_of_nonneg_right hβ (abs_nonneg _)) (by simp)
    linarith [abs_add_le (β * g i) (y' i), ih hy']


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.dotProduct_le_verifyZonoSupportUpFloat {Z : LinearSys.VerifyZono 𝕋 q}
    {x : Vec ℝ q} (hx : x ∈ Z.toSet) (ℓ w : Vec 𝕋 q) {ℓr : Vec ℝ q}
    (hw : ∀ i, |ℓr i - toReal (ℓ i)| ≤ toReal (w i)) : -- --- CONCL ---
    ℓr ⬝ᵥ x ≤ toReal (LinearSys.verifyZonoSupportUpFloat Z ℓ w) := by -- --- PROOF ---
  obtain ⟨y, hy, e, he, rfl⟩ := hx
  -- the generators' part and the magnitudes, rounded up
  set sG := Z.G.foldl (fun acc g =>
    addUp acc (maximum (absolute (dotUp ℓ g)) (absolute (dotDown ℓ g)))) zero with hsG
  set μ : Vec 𝕋 q := fun i => addUp (absolute (Z.c i))
    (Z.G.foldl (fun acc g => addUp acc (absolute (g i))) zero) with hμdef
  set δ : Vec ℝ q := ℓr - toRealVec ℓ with hδ
  have hℓ : ℓr = toRealVec ℓ + δ := by rw [hδ]; abel
  -- `ℓ̃'c`, `ℓ̃' Σⱼ βⱼ gⱼ`, `ℓ̃'e` and `δ'x`
  have h1 : toRealVec ℓ ⬝ᵥ toRealVec Z.c ≤ toReal (dotUp ℓ Z.c) := le_dotUp ℓ Z.c
  have h2 : toRealVec ℓ ⬝ᵥ y ≤ toReal sG := by
    refine le_trans (LinearSys.aux_genSet_dot_le _ _ hy) ?_
    refine le_trans ?_ (LinearSys.aux_le_foldl_addUp _ Z.G zero)
    rw [toReal_zero, zero_add, List.map_map]
    refine List.sum_le_sum fun g _ => ?_
    simp only [Function.comp_apply, toReal_maximum, toReal_absolute]
    have hl := dotDown_le ℓ g
    have hu := le_dotUp ℓ g
    have : toRealVec ℓ ⬝ᵥ toRealVec g = ∑ k, toReal (ℓ k) * toReal (g k) := rfl
    rw [this]
    rw [max_comm]; exact abs_le_max_abs_abs hl hu
  -- the box along `ℓ̃`
  have h3 : toRealVec ℓ ⬝ᵥ e ≤ toReal (dotUp (fun i => absolute (ℓ i)) Z.r) := by
    refine le_trans ?_ (le_dotUp _ _)
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [toRealVec, toReal_absolute]
    calc toReal (ℓ i) * e i ≤ |toReal (ℓ i) * e i| := le_abs_self _
      _ = |toReal (ℓ i)| * |e i| := abs_mul _ _
      _ ≤ |toReal (ℓ i)| * toReal (Z.r i) := mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
  have h4 : δ ⬝ᵥ (toRealVec Z.c + y + e) ≤ toReal (dotUp w fun i => addUp (μ i) (Z.r i)) := by
    refine le_trans ?_ (le_dotUp _ _)
    refine Finset.sum_le_sum fun i _ => ?_
    have hwi : |δ i| ≤ toReal (w i) := hw i
    -- `|xᵢ| ≤ μᵢ + rᵢ`
    have hμ : |(toRealVec Z.c + y + e) i| ≤ toReal (addUp (μ i) (Z.r i)) := by
      have hyi := LinearSys.aux_genSet_abs_le i _ hy
      have hf := LinearSys.aux_le_foldl_addUp (fun g : Vec 𝕋 q => absolute (g i)) Z.G zero
      rw [toReal_zero, zero_add] at hf
      -- the span's entry within the generators' magnitudes
      have hf' : ((Z.G.map toRealVec).map fun g => |g i|).sum
          = (Z.G.map fun g => toReal (absolute (g i))).sum := by
        rw [List.map_map]; congr 1; apply List.map_congr_left; intro g _
        simp [toRealVec, toReal_absolute]
      have ha : toReal (absolute (Z.c i))
          + toReal (Z.G.foldl (fun acc g => addUp acc (absolute (g i))) zero) ≤ toReal (μ i) :=
        add_le_addUp _ _
      have hb := add_le_addUp (μ i) (Z.r i)
      rw [toReal_absolute] at ha
      simp only [Pi.add_apply, toRealVec]
      have := abs_add_le (toReal (Z.c i) + y i) (e i)
      have := abs_add_le (toReal (Z.c i)) (y i)
      linarith [he i]
    calc δ i * (toRealVec Z.c + y + e) i ≤ |δ i| * |(toRealVec Z.c + y + e) i| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ toReal (w i) * toReal (addUp (μ i) (Z.r i)) :=
          mul_le_mul hwi hμ (abs_nonneg _) (le_trans (abs_nonneg _) hwi)
  -- the four parts against the bound rounded up
  rw [hℓ, add_dotProduct, dotProduct_add, dotProduct_add]
  show _ ≤ toReal (addUp (addUp (addUp (dotUp ℓ Z.c) sG) (dotUp (fun i => absolute (ℓ i)) Z.r))
    (dotUp w fun i => addUp (μ i) (Z.r i)))
  linarith [add_le_addUp (addUp (addUp (dotUp ℓ Z.c) sG)
      (dotUp (fun i => absolute (ℓ i)) Z.r)) (dotUp w fun i => addUp (μ i) (Z.r i)),
    add_le_addUp (addUp (dotUp ℓ Z.c) sG)
      (dotUp (fun i => absolute (ℓ i)) Z.r),
    add_le_addUp (dotUp ℓ Z.c) sG]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

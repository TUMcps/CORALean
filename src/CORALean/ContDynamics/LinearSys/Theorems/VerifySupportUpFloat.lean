module

public import CORALean.ContDynamics.LinearSys.Operations.VerifySupportUpFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsDotProductLeWeightedSum
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `LinearSys.verifySupportUpFloat` bounds the support along the exact direction

For every point `x = c + G b`, `‖b‖∞ ≤ 1`, of the initial set: `ℓ x = ℓ̃ x + (ℓ − ℓ̃) x`. The first
part is `ℓ̃'c + Σⱼ (ℓ̃' gⱼ) bⱼ`, each dot product between its sums rounded down and up; the second
is at most `(Σᵢ |ℓ − ℓ̃|ᵢ sᵢ) β ≤ E β` (`MatExp.abs_dotProduct_le_weightedSum`), as every
`|xᵢ| ≤ |cᵢ| + Σⱼ |gᵢⱼ| ≤ β sᵢ`.

## Inputs
* `c` – float center
* `G` – float generators
* `β` – float scaled bound of the initial set
* `s` – float scales
* `ℓ` – float direction
* `E` – float error of the direction
* `ℓr` – exact direction
* `b` – factors of the point

## Hypotheses
* `hβ0` – `β` is nonnegative
* `hβ` – every `|cᵢ| + Σⱼ |gᵢⱼ|` is at most `β sᵢ`
* `hE` – the weighted error of `ℓ̃` is at most `E`
* `hb` – the factors lie in `[-1, 1]`

## Conclusion
* `ℓ (c + G b)` is at most the float bound
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

/-- `|x|` of a real between two floats is at most the larger float magnitude. -/
private theorem LinearSys.aux_abs_le_max {lo hi : 𝕋} {x : ℝ} (h1 : toReal lo ≤ x)
    (h2 : x ≤ toReal hi) :
    |x| ≤ toReal (maximum (absolute hi) (absolute lo)) := by
  rw [toReal_maximum, toReal_absolute, toReal_absolute, max_comm]
  exact abs_le_max_abs_abs h1 h2


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.dotProduct_le_verifySupportUpFloat (c : Vec 𝕋 n) (G : Mat 𝕋 n m) {β : 𝕋}
    {s : Vec 𝕋 n} (hβ0 : 0 ≤ toReal β)
    (hβ : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal β * toReal (s i))
    (ℓ : Vec 𝕋 n) {E : 𝕋} {ℓr : Vec ℝ n}
    (hE : ∑ i, |ℓr i - toReal (ℓ i)| * toReal (s i) ≤ toReal E) {b : Fin m → ℝ}
    (hb : ∀ j, |b j| ≤ 1) : -- --- CONCL ---
    ℓr ⬝ᵥ (toRealVec c + toRealMat G *ᵥ b)
      ≤ toReal (LinearSys.verifySupportUpFloat c G β ℓ E) := by -- --- PROOF ---
  set x := toRealVec c + toRealMat G *ᵥ b with hx
  set g : Fin m → 𝕋 := fun j => maximum (absolute (dotUp ℓ fun i => G i j))
    (absolute (dotDown ℓ fun i => G i j)) with hg
  -- `|xᵢ| ≤ β sᵢ`
  have hxi : ∀ i, |x i| ≤ toReal β * toReal (s i) := by
    intro i
    refine le_trans ?_ (hβ i)
    have hGb : |(toRealMat G *ᵥ b) i| ≤ ∑ j, |toReal (G i j)| := by
      show |∑ j, toRealMat G i j * b j| ≤ _
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hb j)
    simp only [hx, Pi.add_apply, toRealVec]
    exact le_trans (abs_add_le _ _) (add_le_add le_rfl hGb)
  -- the error part
  have herr : (ℓr - toRealVec ℓ) ⬝ᵥ x ≤ toReal (mulUp E β) := by
    have h := Real.MatExp.abs_dotProduct_le_weightedSum (ℓr - toRealVec ℓ) x (toRealVec s) hxi
    simp only [Pi.sub_apply, toRealVec] at h
    refine le_trans (le_abs_self _) (le_trans h (le_trans ?_ (mul_le_mulUp _ _)))
    exact mul_le_mul_of_nonneg_right hE hβ0
  -- the float direction's part: the center and each generator's term
  have hgen : ∀ j, (∑ i, toReal (ℓ i) * toReal (G i j)) * b j ≤ toReal (g j) := by
    intro j
    have h1 := dotDown_le ℓ fun i => G i j
    have h2 := le_dotUp ℓ fun i => G i j
    refine le_trans (le_trans (le_abs_self _) ?_) (LinearSys.aux_abs_le_max h1 h2)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hb j)
  -- the float direction's part: the center's and the generators' sums
  have hmain : toRealVec ℓ ⬝ᵥ x
      ≤ toReal (dotUp ℓ c) + toReal (sumUp g) := by
    have hdot : toRealVec ℓ ⬝ᵥ x = toRealVec ℓ ⬝ᵥ toRealVec c
        + ∑ j, (∑ i, toReal (ℓ i) * toReal (G i j)) * b j := by
      rw [hx, dotProduct_add, dotProduct_mulVec]
      rfl
    rw [hdot]
    exact add_le_add (le_dotUp ℓ c)
      (le_trans (Finset.sum_le_sum fun j _ => hgen j) (sum_le_sumUp g))
  have hsplit : ℓr ⬝ᵥ x = toRealVec ℓ ⬝ᵥ x + (ℓr - toRealVec ℓ) ⬝ᵥ x := by
    rw [← add_dotProduct, add_sub_cancel]
  -- both parts, added up and rounded up
  rw [hsplit]
  unfold LinearSys.verifySupportUpFloat
  simp only [← hg]
  have ha1 := add_le_addUp (dotUp ℓ c) (sumUp g)
  have ha2 := add_le_addUp (addUp (dotUp ℓ c) (sumUp g)) (mulUp E β)
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

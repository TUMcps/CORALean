module

public import CORALean.Global.Float.PowDown
public import CORALean.Global.Float.PowUp
public import CORALean.Specification.SyntaxTree.Operations.NthrootFloat

@[expose] public section

/-!
# `nthrootFloat` contains the root

The interval `SyntaxTree.nthrootFloat` holds the real `k`-th root of the number it is given. The
bracket ends it keeps satisfy their power inequality at every bisection step, so the lower end is at
most, and the upper end at least, the root of `|x|`; a negative number reflects them, and an unknown
sign takes the hull.

## Inputs
* `steps` – bisection steps
* `x` – number
* `k` – degree

## Hypotheses
* none

## Conclusion
* the root lies between the bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The lower end keeps a nonnegative value whose power is at most `x`. -/
theorem SyntaxTree.aux_downIter_invFloat (x : 𝕋) (k : ℕ) : -- --- CONCL ---
    ∀ (n : ℕ) (lo hi : 𝕋), 0 ≤ toReal lo → toReal lo ^ k ≤ toReal x → 0 ≤ toReal
      (SyntaxTree.aux_nthrootFloat_downIter x k n lo hi) ∧ toReal
      (SyntaxTree.aux_nthrootFloat_downIter x k n lo hi) ^ k ≤ toReal x := by -- --- PROOF ---
  intro n
  induction n with
  | zero => intro lo hi h0 h1; exact ⟨h0, h1⟩
  | succ n ih =>
    intro lo hi h0 h1
    have hm : 0 ≤ toReal (maximum zero (half (addDown lo hi))) := by
      rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
    unfold SyntaxTree.aux_nthrootFloat_downIter
    dsimp only
    split_ifs with hc
    · refine ih _ _ hm ?_
      refine (le_powUp hm le_rfl k).trans ((toReal_le_of_le hc))
    · exact ih _ _ h0 h1

/-- The upper end keeps a nonnegative value whose power is at least `x`. -/
theorem SyntaxTree.aux_upIter_invFloat (x : 𝕋) (k : ℕ) : -- --- CONCL ---
    ∀ (n : ℕ) (lo hi : 𝕋), 0 ≤ toReal hi → toReal x ≤ toReal hi ^ k → 0 ≤ toReal
      (SyntaxTree.aux_nthrootFloat_upIter x k n lo hi) ∧ toReal x ≤ toReal
      (SyntaxTree.aux_nthrootFloat_upIter x k n lo hi) ^ k := by -- --- PROOF ---
  intro n
  induction n with
  | zero => intro lo hi h0 h1; exact ⟨h0, h1⟩
  | succ n ih =>
    intro lo hi h0 h1
    have hm : 0 ≤ toReal (maximum zero (half (addUp lo hi))) := by
      rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
    unfold SyntaxTree.aux_nthrootFloat_upIter
    dsimp only
    split_ifs with hc
    · refine ih _ _ hm ?_
      exact (toReal_le_of_le hc).trans (powDown_le hm le_rfl k)
    · exact ih _ _ h0 h1

/-- For a nonnegative `x` and a degree at least one, the lower end is at most the root. -/
theorem SyntaxTree.aux_down_leFloat {steps k : ℕ} {x : 𝕋} (hk : 0 < k)
    (hx : 0 ≤ toReal x) : -- --- CONCL ---
    toReal (SyntaxTree.aux_nthrootFloat_down steps x k) ≤
      toReal x ^ ((1 : ℝ) / k) := by -- --- PROOF ---
  have h := SyntaxTree.aux_downIter_invFloat x k steps (zero : 𝕋) (maximum one x)
    (by rw [toReal_zero]) (by rw [toReal_zero, zero_pow hk.ne']; exact hx)
  unfold SyntaxTree.aux_nthrootFloat_down
  rw [one_div, Real.le_rpow_inv_iff_of_pos h.1 hx (by exact_mod_cast hk), Real.rpow_natCast]
  exact h.2

/-- For a nonnegative `x` and a degree at least one, the upper end is at least the root. -/
theorem SyntaxTree.aux_le_upFloat {steps k : ℕ} {x : 𝕋} (hk : 0 < k)
    (hx : 0 ≤ toReal x) : -- --- CONCL ---
    toReal x ^ ((1 : ℝ) / k) ≤
      toReal (SyntaxTree.aux_nthrootFloat_up steps x k) := by -- --- PROOF ---
  have h1 : 1 ≤ toReal (maximum one x) := by rw [toReal_maximum, toReal_one]; exact le_max_left _ _
  have h := SyntaxTree.aux_upIter_invFloat x k steps (zero : 𝕋) (maximum one x) (by linarith)
    (by
      calc toReal x ≤ toReal (maximum one x) := by rw [toReal_maximum]; exact le_max_right _ _
        _ ≤ toReal (maximum one x) ^ k := le_self_pow₀ h1 hk.ne')
  unfold SyntaxTree.aux_nthrootFloat_up
  rw [one_div, Real.rpow_inv_le_iff_of_pos hx h.1 (by exact_mod_cast hk), Real.rpow_natCast]
  exact h.2

/-- The real root of a nonpositive number reflects the root of its negative. -/
theorem SyntaxTree.aux_nthroot_of_nonposFloat {x : ℝ} (hx : x ≤ 0) (k : ℕ)
    (hk : 0 < k) : -- --- CONCL ---
    SyntaxTree.nthroot x k = -((-x) ^ ((1 : ℝ) / k)) := by -- --- PROOF ---
  unfold SyntaxTree.nthroot
  split_ifs with h
  · have : x = 0 := le_antisymm hx h
    subst this
    simp only [neg_zero]
    rw [Real.zero_rpow (one_div_ne_zero (Nat.cast_ne_zero.2 hk.ne')), neg_zero]
  · rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of `nthrootFloat` holds the real root of the number. -/
theorem SyntaxTree.nthrootFloat_contains (steps : ℕ) (x : 𝕋) (k : ℕ) : -- --- CONCL ---
    toReal (SyntaxTree.nthrootFloat steps x k).inf ≤ SyntaxTree.nthroot (toReal x) k ∧
      SyntaxTree.nthroot (toReal x) k ≤
        toReal (SyntaxTree.nthrootFloat steps x k).sup := by -- --- PROOF ---
  unfold SyntaxTree.nthrootFloat
  by_cases hk : k = 0
  · subst hk
    simp only [if_true, toReal_neg, toReal_one, SyntaxTree.nthroot]
    split_ifs <;> norm_num
  have hk' : 0 < k := Nat.pos_of_ne_zero hk
  rw [if_neg hk]
-- a nonnegative number: the bracket ends bound its root
  by_cases h0 : le zero x = true
  · rw [if_pos h0]
    have hx : 0 ≤ toReal x := by simpa [toReal_zero] using toReal_le_of_le h0
    unfold SyntaxTree.nthroot
    rw [if_pos hx]
    exact ⟨SyntaxTree.aux_down_leFloat hk' hx, SyntaxTree.aux_le_upFloat hk' hx⟩
  rw [if_neg h0]
-- a nonpositive number reflects the roots of its negative
  by_cases h1 : le x zero = true
  · rw [if_pos h1]
    have hx : toReal x ≤ 0 := by simpa [toReal_zero] using toReal_le_of_le h1
    rw [SyntaxTree.aux_nthroot_of_nonposFloat hx k hk']
    have hn : 0 ≤ toReal (neg x) := by rw [toReal_neg]; linarith
    have a := SyntaxTree.aux_down_leFloat (steps := steps) hk' hn
    have b := SyntaxTree.aux_le_upFloat (steps := steps) hk' hn
    rw [toReal_neg] at a b
    simp only [toReal_neg]
    exact ⟨by linarith, by linarith⟩
-- a number of unknown sign takes the hull of the roots of its absolute value
  · rw [if_neg h1]
    have hn : 0 ≤ toReal (absolute x) := by rw [toReal_absolute]; exact abs_nonneg _
    have b := SyntaxTree.aux_le_upFloat (steps := steps) hk' hn
    rw [toReal_absolute] at b
    have hpos : 0 ≤ |toReal x| ^ ((1 : ℝ) / k) := Real.rpow_nonneg (abs_nonneg _) _
    simp only [toReal_neg]
    unfold SyntaxTree.nthroot
    split_ifs with h
    · rw [abs_of_nonneg h] at b hpos
      exact ⟨by linarith [b], by linarith [b]⟩
    · rw [abs_of_neg (not_le.1 h)] at b hpos
      exact ⟨by linarith [b], by linarith [b]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

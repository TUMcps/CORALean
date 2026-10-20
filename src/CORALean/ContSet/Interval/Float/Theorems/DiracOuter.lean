module

public import CORALean.ContSet.Interval.Float.Operations.Dirac
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# `Interval.dirac` encloses, over a floating-point scalar

Outer, at `n = 0`: the value of `δ` at every point of the box (`∞` at `0`, else `0`) lies in the
result. At `n ≥ 1` the value at `0` is a distribution, not a number, and nothing is stated. No
exactness is claimed where `0` is in the box.

## Inputs
* `I` – interval box
* `x` – real point
* `i` – coordinate index

## Hypotheses
* `hx` – `x` lies in the box

## Conclusion
* the open-ended bounds enclose the Dirac value at every coordinate
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Interval.aux_dirac_miss {I : Interval (Vec 𝕋 m)} {i : Fin m}
    (h : (ltStrict zero (I.inf i) || ltStrict (I.sup i) zero) = true) :
    0 < toReal (I.inf i) ∨ toReal (I.sup i) < 0 := by
  rcases Bool.or_eq_true_iff.1 h with h | h
  · left; simpa [toReal_zero] using toReal_lt_of_ltStrict h
  · right; simpa [toReal_zero] using toReal_lt_of_ltStrict h


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.dirac_zero_outer (I : Interval (Vec 𝕋 m)) {x : Vec ℝ m}
    (hx : x ∈ I.construct) (i : Fin m) : -- --- CONCL ---
    (∀ l, (Interval.dirac 0 I).lo i = some l →
        ((toReal l : ℝ) : EReal) ≤ (if x i = 0 then ⊤ else 0)) ∧
      ∀ u, (Interval.dirac 0 I).hi i = some u →
        (if x i = 0 then ⊤ else 0) ≤ ((toReal u : ℝ) : EReal) := by -- --- PROOF ---
  unfold Interval.dirac
  constructor
  · -- the lower end is `0`, below both values of `δ`
    intro l hl
    have : l = zero := by dsimp only at hl; split_ifs at hl; exact (Option.some.inj hl).symm
    subst this
    rw [toReal_zero]
    by_cases h : x i = 0
    · simp [h]
    · simp [h]
  · intro u hu
    by_cases hm : (ltStrict zero (I.inf i) || ltStrict (I.sup i) zero) = true
    · -- a finite upper end only where the box misses `0`, where `δ = 0`
      have hu' : u = zero := by
        dsimp only at hu; simp only [hm, if_true] at hu; exact (Option.some.inj hu).symm
      subst hu'
      have hne : x i ≠ 0 := by
        rcases Interval.aux_dirac_miss hm with h | h
        · exact ne_of_gt (lt_of_lt_of_le h (hx i).1)
        · exact ne_of_lt (lt_of_le_of_lt (hx i).2 h)
      simp [hne, toReal_zero]
    · dsimp only at hu
      simp only [hm] at hu
      exact absurd hu (by simp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

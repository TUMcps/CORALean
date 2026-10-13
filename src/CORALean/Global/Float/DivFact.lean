module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# Dividing by a factorial, enclosed

`q / k!` from an enclosure `q` of a non-negative number, dividing by `1, 2, …, k` in turn:
the lower end by `j` rounded up, the upper end by `j` rounded down and floored at one, so
every divisor is positive and `div_le_divUp`'s hypothesis holds. The coefficients of an
expansion, `g⁽ᵏ⁾(c) / k!`, and `1 / (N+1)!` in a Lagrange remainder, are this.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def divFact (q : 𝕋 × 𝕋) : ℕ → 𝕋 × 𝕋
  | 0 => q
  | k + 1 => (divDown (divFact q k).1 (nsmulUp (k + 1) one),
      divUp (divFact q k).2 (maximum one (nsmulDown (k + 1) one)))

theorem divFact_mem [SoundFloatArithmetic 𝕋] (q : 𝕋 × 𝕋) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : toReal q.1 ≤ a ∧ a ≤ toReal q.2) :
    ∀ k : ℕ, toReal (divFact q k).1 ≤ a / (k.factorial : ℝ) ∧
      a / (k.factorial : ℝ) ≤ toReal (divFact q k).2 := by -- --- PROOF ---
  intro k
  induction k with
  | zero => simpa [divFact] using ha
  | succ k ih =>
    have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hb : 0 ≤ a / (k.factorial : ℝ) := div_nonneg ha0 hk.le
    -- the two roundings of `k + 1`, the lower one floored at one
    have hU : ((k + 1 : ℕ) : ℝ) * 1 ≤ toReal (nsmulUp (k + 1) (one : 𝕋)) := by
      have := le_nsmulUp (k + 1) (one : 𝕋); rwa [toReal_one] at this
    have hD : toReal (nsmulDown (k + 1) (one : 𝕋)) ≤ ((k + 1 : ℕ) : ℝ) * 1 := by
      have := nsmulDown_le (k + 1) (one : 𝕋); rwa [toReal_one] at this
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have hUpos : (0 : ℝ) < toReal (nsmulUp (k + 1) (one : 𝕋)) := by linarith
    have hm : toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) =
        max 1 (toReal (nsmulDown (k + 1) (one : 𝕋))) := by rw [toReal_maximum, toReal_one]
    have hm1 : (1 : ℝ) ≤ toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) := by
      rw [hm]; exact le_max_left _ _
    have hmk : toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) ≤ ((k + 1 : ℕ) : ℝ) := by
      rw [hm]; exact max_le hk1 (by linarith)
    have heq : a / ((k + 1).factorial : ℝ) = a / (k.factorial : ℝ) / ((k + 1 : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, div_div, mul_comm]
    rw [heq]
    -- each end: the previous bound, divided by a divisor on the right side of `k + 1`
    constructor
    · refine le_trans (divDown_le_div _ _ hUpos) ?_
      calc toReal (divFact q k).1 / toReal (nsmulUp (k + 1) (one : 𝕋))
          ≤ a / (k.factorial : ℝ) / toReal (nsmulUp (k + 1) (one : 𝕋)) :=
            div_le_div_of_nonneg_right ih.1 hUpos.le
        _ ≤ _ := div_le_div_of_nonneg_left hb (by linarith) (by linarith)
    · refine le_trans ?_ (div_le_divUp _ _ (by linarith))
      calc a / (k.factorial : ℝ) / ((k + 1 : ℕ) : ℝ)
          ≤ a / (k.factorial : ℝ) / toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) :=
            div_le_div_of_nonneg_left hb (by linarith) hmk
        _ ≤ _ := div_le_div_of_nonneg_right ih.2 (by linarith)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

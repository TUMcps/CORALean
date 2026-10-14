module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `Interval.halve` contains half of every vector in the box
Exact: the bounds are halved exactly (`toReal_half`), so `(1/2) • x` lies in the halved box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.halve_outer {I : Interval (Vec 𝕋 n)} {x : Vec ℝ n} (hx : x ∈ I.construct) :
    (1 / 2 : ℝ) • x ∈ (Interval.halve I).construct := by -- --- PROOF ---
  intro i
  have h : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  show toReal (half (I.inf i)) ≤ ((1 / 2 : ℝ) • x) i ∧ ((1 / 2 : ℝ) • x) i ≤ toReal (half (I.sup i))
  rw [toReal_half, toReal_half]
  simp only [Pi.smul_apply, smul_eq_mul]
  constructor <;> linarith [h.1, h.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

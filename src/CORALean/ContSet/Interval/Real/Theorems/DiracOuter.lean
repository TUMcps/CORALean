import CORALean.ContSet.Interval.Real.Theorems.DiracZeroMem
import Mathlib.Data.Sign.Basic

/-!
# `Interval.dirac` encloses at `n = 0`

At `n = 0` the value of `δ` at `0` is `∞`, and the box reaches it wherever `0` is in the
interval: with `δ(t) = ∞` for `t = 0` and `0` otherwise, every point of the box has its `δ`
value in the result. Outer only: the result is `[0, ∞)` where `δ` takes the two values `0` and
`∞`, so no exactness is claimed. At `n ≥ 1` the value at `0` is a distribution, not a number, and
nothing is stated there (`dirac_zero_mem` says the result contains `0`, the value off `0`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The value of `δ` at `t`: `∞` at `0`, `0` elsewhere. -/
noncomputable def Interval.aux_diracValue (t : ℝ) : EReal := by
  classical
  exact if t = 0 then ⊤ else 0


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.dirac_zero_outer (I : Interval (Vec ℝ m)) {x : Vec ℝ m} (hx : x ∈ I.construct)
    (i : Fin m) :
    (Interval.dirac 0 I).1 i ≤ Interval.aux_diracValue (x i) ∧
      Interval.aux_diracValue (x i) ≤ (Interval.dirac 0 I).2 i := by -- --- PROOF ---
  classical
  have hx0 := Interval.dirac_zero_mem 0 I i
  by_cases h : x i = 0
  · -- `0` is in the interval: the signs of its bounds sum to at most `1` in absolute value
    have hi : I.inf i ≤ x i ∧ x i ≤ I.sup i := hx i
    rw [h] at hi
    have hv : Interval.aux_diracValue (x i) = ⊤ := by simp [Interval.aux_diracValue, h]
    rw [hv]
    refine ⟨le_top, ?_⟩
    have hsup : 0 < I.sup i ∨ I.sup i = 0 := hi.2.lt_or_eq.imp id Eq.symm
    rcases hi.1.lt_or_eq with h1 | h1 <;> rcases hsup with h2 | h2 <;>
      norm_num [Interval.dirac, h1, h2, sign_neg, sign_pos]
  · -- off `0` the value is `0`, which the result contains
    have hv : Interval.aux_diracValue (x i) = 0 := by simp [Interval.aux_diracValue, h]
    rw [hv]
    exact hx0


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

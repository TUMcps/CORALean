module

public import CORALean.ContSet.Interval.Float.Operations.Log
public import CORALean.ContSet.Interval.Real.Theorems.LogExact

@[expose] public section

/-!
# `Interval.log` contains the image under the logarithm

`logUp` holds at every positive argument, `logDown` only from `1 ≤ a ≤ 2 ^ p / 2` (`logDown_le`),
so the theorem asks that of every lower bound. A box with a lower bound below `1` is not covered.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.log_outer [SoundFloatArithmetic 𝕋] (p k : ℕ) (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, 1 ≤ toReal (I.inf i) ∧ toReal (I.inf i) ≤ 2 ^ p / 2) :
    (fun x i => Real.log (x i)) '' I.construct ⊆ (I.log p k).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  have h1 : 1 ≤ x i := le_trans (hI i).1 hx'.1
  have hpos : 0 < toReal (I.sup i) := lt_of_lt_of_le zero_lt_one (h1.trans hx'.2)
  exact ⟨le_trans (logDown_le p k _ (hI i).1 (hI i).2)
      (Real.log_le_log (lt_of_lt_of_le zero_lt_one (hI i).1) hx'.1),
    le_trans (Real.log_le_log (lt_of_lt_of_le zero_lt_one h1) hx'.2) (le_logUp p k _ hpos)⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

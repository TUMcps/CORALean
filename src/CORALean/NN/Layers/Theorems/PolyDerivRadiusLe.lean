module

public import CORALean.NN.Layers.Definitions.PolyDerivBound
public import CORALean.NN.Layers.Operations.PolyDerivRadiusUp
public import CORALean.NN.Layers.Theorems.PowRangeBounds
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# A stored radius bounds the exact one

Each term rounded up: the box's worse end, the degree count from above, the coefficient exactly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem polyDerivRadius_le (c : Fin (n + 1) → 𝕋) (l u : 𝕋) :
    Real.polyDerivRadius (fun k => toReal (c k)) (toReal l) (toReal u)
      ≤ toReal (polyDerivRadiusUp c l u) := by -- --- PROOF ---
  show (∑ i : Fin (n + 1), if (i : ℕ) = 1 then (0 : ℝ)
    else |toReal (c i)| * (i : ℕ) * max |toReal l| |toReal u| ^ ((i : ℕ) - 1)) ≤ _
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
  by_cases hi : (i : ℕ) = 1
  · rw [if_pos hi, if_pos hi, toReal_zero]
  · rw [if_neg hi, if_neg hi]
    -- the box's worse end, the degree count from above, and the coefficient exactly
    have hm : toReal (maximum (absolute l) (absolute u)) = max |toReal l| |toReal u| := by
      rw [toReal_maximum, toReal_absolute, toReal_absolute]
    have hp := (powRange_bounds (maximum (absolute l) (absolute u)) ((i : ℕ) - 1)).2
    rw [hm] at hp
    have hnat : ((i : ℕ) : ℝ) ≤ toReal (nsmulUp (i : ℕ) (one : 𝕋)) := by
      have hn := le_nsmulUp (i : ℕ) (one : 𝕋)
      rwa [toReal_one, mul_one] at hn
    have h1 : |toReal (c i)| * ((i : ℕ) : ℝ)
        ≤ toReal (mulUp (absolute (c i)) (nsmulUp (i : ℕ) one)) := by
      refine le_trans ?_ (mul_le_mulUp _ _)
      rw [toReal_absolute]
      exact mul_le_mul_of_nonneg_left hnat (abs_nonneg _)
    have h0 : (0 : ℝ) ≤ |toReal (c i)| * ((i : ℕ) : ℝ) :=
      mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
    refine le_trans (mul_le_mul h1 hp (by positivity) (le_trans h0 h1)) (mul_le_mulUp _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

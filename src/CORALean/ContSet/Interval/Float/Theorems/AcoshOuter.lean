module

public import CORALean.ContSet.Interval.Float.Operations.Acosh

@[expose] public section

/-!
# `Interval.acosh` contains the image under `acosh`

## Inputs
* `p` – range exponent of `logDown`
* `k` – bisection and Newton steps
* `I` – interval box

## Hypotheses
* `hI` – lower bounds at least one, within the exponential range

## Conclusion
* the inverse hyperbolic cosine image of `I` lies in the result box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.acosh_outer [SoundFloatArithmetic 𝕋] (p k : ℕ) (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, 1 ≤ toReal (I.inf i) ∧ 2 * toReal (I.inf i) ≤ 2 ^ p / 2) : -- --- CONCL ---
    (fun x i => Real.arcosh (x i)) '' I.construct ⊆ (I.acosh p k).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  have h1 : 1 ≤ x i := le_trans (hI i).1 hx'.1
  have hpos : (0:ℝ) < toReal (I.inf i) := lt_of_lt_of_le one_pos (hI i).1
  exact ⟨le_trans (acoshDown_le p k _ (hI i).1 (hI i).2)
      ((Real.arcosh_le_arcosh hpos (lt_of_lt_of_le hpos hx'.1)).2 hx'.1),
    le_trans ((Real.arcosh_le_arcosh (lt_of_lt_of_le one_pos h1)
      (lt_of_lt_of_le one_pos (h1.trans hx'.2))).2 hx'.2)
      (le_acoshUp p k _ (h1.trans hx'.2))⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

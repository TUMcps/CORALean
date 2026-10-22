module

public import CORALean.ContSet.InflatedContSet.Interfaces

@[expose] public section

/-!
# Composing a nominal part with its box

Set addition is commutative and associative, so the two nominal parts and the
two boxes regroup and each side is weakened once. Every binary operation that
computes its nominal part approximately reduces to this.

The three representations are separately typed, since an operation may take and
return different ones.

## Inputs
* `s₁` – first inflated set
* `s₂` – second inflated set
* `t` – inflated set
* `D` – rounding slack

## Hypotheses
* `hnominal` – sum of nominal parts lies in the nominal part of `t` plus `D`
* `herror` – sum of boxes plus `D` lies in the box of `t`

## Conclusion
* the sum of `s₁` and `s₂` lies in `t`
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S₁ S₂ T N₁ N₂ N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [ContSet N₁ (Vec ℝ n)] [ContSet N₂ (Vec ℝ n)] [ContSet N (Vec ℝ n)]
variable [InflatedContSet S₁ N₁ (Vec 𝕋 n) (Vec ℝ n)]
  [InflatedContSet S₂ N₂ (Vec 𝕋 n) (Vec ℝ n)]
  [InflatedContSet T N (Vec 𝕋 n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem plus_subset {s₁ : S₁} {s₂ : S₂} {t : T} {D : Set (Vec ℝ n)}
    (hnominal : nominalSet s₁ + nominalSet s₂ ⊆
      nominalSet t + D)
    (herror : (I_error s₁).construct + (I_error s₂).construct + D ⊆ (I_error t).construct)
    : -- --- CONCL ---
    construct s₁ + construct s₂ ⊆ construct t := by -- --- PROOF ---
  show nominalSet s₁ + (I_error s₁).construct
      + (nominalSet s₂ + (I_error s₂).construct) ⊆
    nominalSet t + (I_error t).construct
  -- the four summands regrouped so each hypothesis applies to one pair
  calc nominalSet s₁ + (I_error s₁).construct
        + (nominalSet s₂ + (I_error s₂).construct)
      = nominalSet s₁ + nominalSet s₂
        + ((I_error s₁).construct + (I_error s₂).construct) := add_add_add_comm _ _ _ _
    _ ⊆ nominalSet t + D
        + ((I_error s₁).construct + (I_error s₂).construct) :=
        Set.add_subset_add_right hnominal
    _ = nominalSet t
        + ((I_error s₁).construct + (I_error s₂).construct + D) := by
        rw [add_assoc, add_comm D _]
    _ ⊆ nominalSet t + (I_error t).construct :=
        Set.add_subset_add_left herror

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

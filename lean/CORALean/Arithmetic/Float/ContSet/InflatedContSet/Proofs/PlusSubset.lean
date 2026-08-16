import CORALean.Arithmetic.Float.ContSet.InflatedContSet.API

/-!
# Composing a nominal part with its box

Set addition is commutative and associative, so the two nominal parts and the
two boxes regroup and each side is weakened once. Every binary operation that
computes its nominal part approximately reduces to this.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.InflatedContSet.Proofs

open Pointwise

variable {F S : Type} [FloatOps F] [SoundFloatArithmetic F] {n : ℕ}
variable [InflatedContSet S F n]

theorem plus_subset {s₁ s₂ t : S} {D : Set (Vec ℝ n)}
    (hnominal : nominal s₁ + nominal s₂ ⊆ nominal t + D)
    (herror : (error s₁).construct + (error s₂).construct + D ⊆ (error t).construct) :
    construct s₁ + construct s₂ ⊆ construct t := by
  show nominal s₁ + (error s₁).construct + (nominal s₂ + (error s₂).construct) ⊆
    nominal t + (error t).construct
  calc nominal s₁ + (error s₁).construct + (nominal s₂ + (error s₂).construct)
      = nominal s₁ + nominal s₂ + ((error s₁).construct + (error s₂).construct) :=
        add_add_add_comm _ _ _ _
    _ ⊆ nominal t + D + ((error s₁).construct + (error s₂).construct) :=
        Set.add_subset_add_right hnominal
    _ = nominal t + ((error s₁).construct + (error s₂).construct + D) := by
        rw [add_assoc, add_comm D _]
    _ ⊆ nominal t + (error t).construct := Set.add_subset_add_left herror

end CORALean.Arithmetic.Float.InflatedContSet.Proofs

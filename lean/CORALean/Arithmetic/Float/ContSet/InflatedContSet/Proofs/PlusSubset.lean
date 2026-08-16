import CORALean.Arithmetic.Float.ContSet.InflatedContSet.API

/-!
# Composing a nominal part with its box

Set addition is commutative and associative, so the two nominal parts and the
two boxes regroup and each side is weakened once. Every binary operation that
computes its nominal part approximately reduces to this.

The three representations are separately typed: a zonotope `plus` returns
`h + k` generators, so its arguments and its result are three different types
that agree only on the dimension.

`nominalSet s` is `s.nominal.construct`, which cannot be written that way here:
`Nᵢ` is a type variable and dot notation resolves through a type's head
constant. A representation's own proofs, where it is concrete, write
`(nominal Z).construct`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.InflatedContSet.Proofs

open Pointwise

variable {F S₁ S₂ T N₁ N₂ N : Type} [FloatOps F] [SoundFloatArithmetic F] {n : ℕ}
variable [Real.ContSet N₁ n] [Real.ContSet N₂ n] [Real.ContSet N n]
variable [InflatedContSet S₁ N₁ F n] [InflatedContSet S₂ N₂ F n] [InflatedContSet T N F n]

theorem plus_subset {s₁ : S₁} {s₂ : S₂} {t : T} {D : Set (Vec ℝ n)}
    (hnominal : nominalSet s₁ + nominalSet s₂ ⊆
      nominalSet t + D)
    (herror : (error s₁).construct + (error s₂).construct + D ⊆ (error t).construct) :
    construct s₁ + construct s₂ ⊆ construct t := by
  show nominalSet s₁ + (error s₁).construct
      + (nominalSet s₂ + (error s₂).construct) ⊆
    nominalSet t + (error t).construct
  calc nominalSet s₁ + (error s₁).construct
        + (nominalSet s₂ + (error s₂).construct)
      = nominalSet s₁ + nominalSet s₂
        + ((error s₁).construct + (error s₂).construct) := add_add_add_comm _ _ _ _
    _ ⊆ nominalSet t + D
        + ((error s₁).construct + (error s₂).construct) :=
        Set.add_subset_add_right hnominal
    _ = nominalSet t
        + ((error s₁).construct + (error s₂).construct + D) := by
        rw [add_assoc, add_comm D _]
    _ ⊆ nominalSet t + (error t).construct :=
        Set.add_subset_add_left herror

end CORALean.Arithmetic.Float.InflatedContSet.Proofs

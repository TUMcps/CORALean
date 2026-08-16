import CORALean.Arithmetic.Float.ContSet.InflatedContSet.API

/-!
# Weakening both parts at once

The degenerate case of `map_subset`, for an operation that is already an
inclusion rather than an image: nominal part into nominal part, box into box,
with nothing moving between them.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.InflatedContSet.Proofs

open Pointwise

variable {F S T N M : Type} [FloatOps F] [SoundFloatArithmetic F] {n : ℕ}
variable [Real.ContSet N n] [Real.ContSet M n]
variable [InflatedContSet S N F n] [InflatedContSet T M F n]

theorem mono_subset {s : S} {t : T} (hnominal : nominalSet s ⊆ nominalSet t)
    (herror : (error s).construct ⊆ (error t).construct) :
    construct s ⊆ construct t :=
  Set.add_subset_add hnominal herror

end CORALean.Arithmetic.Float.InflatedContSet.Proofs

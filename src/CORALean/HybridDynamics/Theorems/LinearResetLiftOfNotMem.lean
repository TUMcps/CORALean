module

public import CORALean.HybridDynamics.Operations.LinearResetLift
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `LinearReset.lift` is the identity off the bound coordinates

A coordinate of the larger space that no `stateBind` entry hits keeps its value when `id` holds
and is `0` otherwise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearReset.lift_of_not_mem (W : Mat 𝕋 n n) (w : Vec 𝕋 n) (stateBind : Fin n → Fin N)
    (id : Bool) (x : Vec ℝ N) (i : Fin N) (hi : ∀ j, stateBind j ≠ i) : -- --- STMT ---
    (toRealMat (LinearReset.lift W w N stateBind id).1 *ᵥ x +
        toRealVec (LinearReset.lift W w N stateBind id).2) i =
      if id then x i else 0 := by -- --- PROOF ---
  -- no source for `i`
  have hnone : (List.finRange n).find? (fun j => stateBind j = i) = none :=
    List.find?_eq_none.2 fun l _ => by simpa using hi l
  simp only [Pi.add_apply, mulVec, dotProduct, toRealMat_apply, toRealVec_apply,
    LinearReset.lift, of_apply, hnone]
  -- the row is `eᵢ` or `0`
  cases id <;> simp [apply_ite (toReal : 𝕋 → ℝ), ExactScalar.toReal_zero,
    ExactScalar.toReal_one]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.Arithmetic.Float.Instances.Dyadic.Proofs

/-!
# What `Dyadic` guarantees

The instance is this representation's `Theorems` file: the class fields *are*
the obligations, one per operation, so there is nothing to restate.

Each is exactness composed with a rounding direction — the two halves proved
separately in `Proofs`, and nothing else needed. In particular no bound on the
mantissa is required: rounding may leave the grid without threatening
soundness, exactly as a bad partition may cost a zonotope precision without
threatening its.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

noncomputable instance {p : ℕ} : SoundFloatArithmetic (Dyadic p) where
  toReal := Dyadic.toReal
  zero := ⟨0, 0⟩
  neg := Dyadic.neg
  addUp := Dyadic.addUp
  addDown := Dyadic.addDown
  mulUp := Dyadic.mulUp
  mulDown := Dyadic.mulDown
  toReal_neg := Dyadic.toReal_neg
  toReal_zero := by rw [Dyadic.toReal, Int.cast_zero, zero_mul]
  add_le_addUp a b := Dyadic.toReal_exactAdd a b ▸ Dyadic.le_roundUp _
  addDown_le_add a b := Dyadic.toReal_exactAdd a b ▸ Dyadic.roundDown_le _
  mul_le_mulUp a b := Dyadic.toReal_exactMul a b ▸ Dyadic.le_roundUp _
  mulDown_le_mul a b := Dyadic.toReal_exactMul a b ▸ Dyadic.roundDown_le _

end CORALean.Arithmetic.Float

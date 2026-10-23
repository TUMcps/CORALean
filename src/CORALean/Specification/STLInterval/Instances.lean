module

public import CORALean.Global.Float.DecidableToReal
public import CORALean.Specification.STLInterval.Definitions.ToEReal

@[expose] public section

/-!
# Comparing upper bounds of STL intervals, decided

An upper bound is a stored scalar or `inf` (`WithTop 𝕋`), read as an extended real by `toEReal`.
How two of them compare is decided by the exact comparison of the scalars (`ExactLe`), `inf`
being above every stored bound, so an operation on intervals over a float scalar may branch on it
and still run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ========================================  INSTANCES  ========================================= --

/-- `toEReal a ≤ toEReal b`: `inf` is above every stored bound, two stored ones compare as reals. -/
instance (a b : WithTop 𝕋) : Decidable (STLInterval.toEReal a ≤ STLInterval.toEReal b) :=
  match a, b with
  | _, none => isTrue le_top
  | none, some y => isFalse (fun h => by
    change (⊤ : EReal) ≤ ((toReal y : ℝ) : EReal) at h
    exact absurd h (not_le.mpr (EReal.coe_lt_top _)))
  | some x, some y => decidable_of_iff (toReal x ≤ toReal y)
    (show _ ↔ ((toReal x : ℝ) : EReal) ≤ ((toReal y : ℝ) : EReal) from EReal.coe_le_coe_iff.symm)

/-- `toEReal a < toEReal b`: the negation of the comparison the other way. -/
instance (a b : WithTop 𝕋) : Decidable (STLInterval.toEReal a < STLInterval.toEReal b) :=
  decidable_of_iff (¬ STLInterval.toEReal b ≤ STLInterval.toEReal a) not_le

/-- `toEReal a = toEReal b`: the comparison both ways. -/
instance (a b : WithTop 𝕋) : Decidable (STLInterval.toEReal a = STLInterval.toEReal b) :=
  decidable_of_iff (STLInterval.toEReal a ≤ STLInterval.toEReal b ∧
    STLInterval.toEReal b ≤ STLInterval.toEReal a) le_antisymm_iff.symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

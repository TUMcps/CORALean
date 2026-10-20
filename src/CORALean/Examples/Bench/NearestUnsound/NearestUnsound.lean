import CORALean.Examples.Bench.NearestUnsound.NearestDyadic
import CORALean.Examples.Bench.NearestUnsound.NearestFloat

/-!
# What "round-to-nearest is sound" would say — and it is FALSE

One property with twelve conjuncts: the six rounding laws `SoundFloatArithmetic` asks of a scalar,
stated of `NearestFloat`'s operations and of `NearestDyadic p`'s at every `p`. Rounding to nearest
lands on whichever side of the exact result is closer, so it satisfies none of them: every field is
false, and at `NearestDyadic` refutable. `Axioms` assumes this anyway, once, so that the unchanged
library runs on the arithmetic CORA uses, the paper's baseline and nothing else. Bundled for the
reason `Binary64.TrustedHardware` is: one name in every `#print axioms` that reaches either scalar.
Everything a round-to-nearest scalar gets right is proved in `Instances`, not assumed here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ========================================  MAIN TYPE  ========================================= --

/-- FALSE in every field. Assumed only by `Axioms`, only for the bench's
round-to-nearest baseline; nothing outside `Examples/Bench/` may reach it. -/
structure NearestUnsound : Prop where
  /-- FALSE: `1 + 2⁻⁶⁰` rounds to `1`, below the exact sum. -/
  float_add_le_addUp : ∀ a b : NearestFloat, a.toReal + b.toReal ≤ (a.add b).toReal
  /-- FALSE: `1 + 3 · 2⁻⁵⁴` rounds up to `1 + 2⁻⁵²`, above the exact sum. -/
  float_addDown_le_add : ∀ a b : NearestFloat, (a.add b).toReal ≤ a.toReal + b.toReal
  /-- FALSE: `0.1 · 10` rounds to `1`, below the exact product of the stored `0.1`
  and `10`. -/
  float_mul_le_mulUp : ∀ a b : NearestFloat, a.toReal * b.toReal ≤ (a.mul b).toReal
  /-- FALSE: the stored `1/3` times `3` is `1 - 2⁻⁵⁴` exactly, a tie that rounds up
  to `1`. -/
  float_mulDown_le_mul : ∀ a b : NearestFloat, (a.mul b).toReal ≤ a.toReal * b.toReal
  /-- FALSE: `1 / 3` rounds down, below the exact quotient. -/
  float_div_le_divUp : ∀ a b : NearestFloat, 0 < b.toReal →
    a.toReal / b.toReal ≤ (a.div b).toReal
  /-- FALSE: `1 / 10` rounds up, above the exact quotient. -/
  float_divDown_le_div : ∀ a b : NearestFloat, 0 < b.toReal →
    (a.div b).toReal ≤ a.toReal / b.toReal
  /-- FALSE, and refutable: at `p = 24`, `1 + 2⁻³⁰` rounds to `1`. -/
  dyadic_add_le_addUp : ∀ {p : ℕ} (a b : NearestDyadic p),
    a.toReal + b.toReal ≤ (a.add b).toReal
  /-- FALSE, and refutable: at `p = 24`, `1 + 3 · 2⁻²⁵` rounds up to `1 + 2⁻²³`. -/
  dyadic_addDown_le_add : ∀ {p : ℕ} (a b : NearestDyadic p),
    (a.add b).toReal ≤ a.toReal + b.toReal
  /-- FALSE, and refutable: at `p = 24`, `(1 + 2⁻²³)²` rounds down to `1 + 2⁻²²`. -/
  dyadic_mul_le_mulUp : ∀ {p : ℕ} (a b : NearestDyadic p),
    a.toReal * b.toReal ≤ (a.mul b).toReal
  /-- FALSE, and refutable: at `p = 24`, the stored `1/25` times `25` rounds up to
  `1`. -/
  dyadic_mulDown_le_mul : ∀ {p : ℕ} (a b : NearestDyadic p),
    (a.mul b).toReal ≤ a.toReal * b.toReal
  /-- FALSE, and refutable: at `p = 24`, `1 / 25` rounds down. -/
  dyadic_div_le_divUp : ∀ {p : ℕ} (a b : NearestDyadic p), 0 < b.toReal →
    a.toReal / b.toReal ≤ (a.div b).toReal
  /-- FALSE, and refutable: at `p = 24`, `1 / 3` rounds up. -/
  dyadic_divDown_le_div : ∀ {p : ℕ} (a b : NearestDyadic p), 0 < b.toReal →
    (a.div b).toReal ≤ a.toReal / b.toReal

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

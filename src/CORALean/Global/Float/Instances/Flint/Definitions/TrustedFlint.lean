module

public import CORALean.Global.Float.Instances.Flint.Operations.AddDown
public import CORALean.Global.Float.Instances.Flint.Operations.AddUp
public import CORALean.Global.Float.Instances.Flint.Operations.DivDown
public import CORALean.Global.Float.Instances.Flint.Operations.DivUp
public import CORALean.Global.Float.Instances.Flint.Operations.MulDown
public import CORALean.Global.Float.Instances.Flint.Operations.MulUp

@[expose] public section

/-!
# What "FLINT is trusted" says

One property with six conjuncts: the directed laws `SoundFloatArithmetic` asks
of the six rounded operations, stated of the `opaque` FLINT calls at every
precision `p`, about the `toReal` that `Flint` defines. The exact operations are
pure Lean and proved, so, unlike `TrustedHardware`, nothing else is trusted.

Bundled for `TrustedHardware`'s reason: one name in every `#print axioms` that
reaches `Flint`, and one thing to discharge should the calls ever be replaced by
proved Lean — `Dyadic p` already satisfies each conjunct as a theorem.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Flint


-- ========================================  MAIN TYPE  ========================================= --

/-- True if FLINT's `arf_add`, `arf_mul` and `arf_div` round as their
documentation says and the shim converts exactly: see `Axioms`. -/
structure TrustedFlint : Prop where
  /-- `arf_add` with `ARF_RND_CEIL` is at least the exact sum. -/
  add_le_addUp : ∀ (p : ℕ) (a b : Flint p), toReal a + toReal b ≤ toReal (addUp p a b)
  /-- `arf_add` with `ARF_RND_FLOOR` is at most the exact sum. -/
  addDown_le_add : ∀ (p : ℕ) (a b : Flint p), toReal (addDown p a b) ≤ toReal a + toReal b
  /-- `arf_mul` with `ARF_RND_CEIL` is at least the exact product. -/
  mul_le_mulUp : ∀ (p : ℕ) (a b : Flint p), toReal a * toReal b ≤ toReal (mulUp p a b)
  /-- `arf_mul` with `ARF_RND_FLOOR` is at most the exact product. -/
  mulDown_le_mul : ∀ (p : ℕ) (a b : Flint p), toReal (mulDown p a b) ≤ toReal a * toReal b
  /-- `arf_div` with `ARF_RND_CEIL` is at least the exact quotient, for a positive
  divisor only: at zero there is no bound to state. -/
  div_le_divUp : ∀ (p : ℕ) (a b : Flint p),
    0 < toReal b → toReal a / toReal b ≤ toReal (divUp p a b)
  /-- `arf_div` with `ARF_RND_FLOOR` is at most the exact quotient, likewise. -/
  divDown_le_div : ∀ (p : ℕ) (a b : Flint p),
    0 < toReal b → toReal (divDown p a b) ≤ toReal a / toReal b

end Flint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

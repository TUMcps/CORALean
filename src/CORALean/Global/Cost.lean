module

public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.GCongr

@[expose] public section

/-!
# What running an operation costs

A `Cost` counts, at unit price, **scalar arithmetic** (one `+`, `-`, `*`, `/`, comparison, `min`,
`max` or absolute value on the scalar a layer computes in) and **writes** (one unit for every
scalar of the result: computed, copied, padded with a zero or placed alike, exponents and
constraint coefficients included). One convention throughout: **a computed entry costs its
arithmetic plus one write, a copied or padded entry costs one write.** Reading is free:
indexing, taking a field and passing a value on cost nothing, and a value held only in a
register, feeding the next operation directly, is not written. A called subroutine is charged
its own cost, which includes the writes of its own result, so a result is not charged again by
its caller. That is why `Zonotope.plusCost` takes the operands' generator counts: the sum writes
`n (1 + h₁ + h₂)` scalars.

A cost is **asserted**, never derived: a Lean `def` says what is computed and never what
computing it costs, so every `…Cost` is read off an operation's definition by hand. Every cost is
an **upper** bound, so bounds compose; one needing the size of the result takes the operand
sizes as arguments. No enclosure guarantee mentions a `Cost`: a count read wrong makes a bound
wrong, never a set.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A count of scalar operations, asserted against the model above rather than
derived from any Lean definition. -/
structure Cost where
  ops : ℕ

namespace Cost

instance : Zero Cost := ⟨⟨0⟩⟩
instance : Add Cost := ⟨fun a b => ⟨a.ops + b.ops⟩⟩
instance : SMul ℕ Cost := ⟨fun k a => ⟨k * a.ops⟩⟩

-- `ops` is the whole content of a `Cost`, so the order lifts through it.
instance : Preorder Cost := Preorder.lift Cost.ops

@[simp] theorem ops_zero : (0 : Cost).ops = 0 := rfl

@[simp] theorem ops_add (a b : Cost) : (a + b).ops = a.ops + b.ops := rfl

@[simp] theorem ops_smul (k : ℕ) (a : Cost) : (k • a).ops = k * a.ops := rfl

@[simp] theorem le_iff {a b : Cost} : a ≤ b ↔ a.ops ≤ b.ops := Iff.rfl

/-- Running one after the other costs at most the sum of what bounds each. -/
theorem add_le_add {a b c d : Cost} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  Nat.add_le_add h₁ h₂

/-- One matrix-vector product `M *ᵥ v` at `m × n`: `m * n` multiplications, `m * (n - 1)`
additions and `m` writes, rounded up to `2 * m * n + m` so that `n = 0` is bounded too. -/
def matVec (m n : ℕ) : Cost := ⟨2 * (m * n) + m⟩

/-- A comparison sort on `k` keys, at `k * (log₂ k + 1)`: merge sort does at most `k * ⌈log₂ k⌉`
comparisons, `Nat.log 2` floors, and the `+ 1` covers the ceiling, `k = 0` and `k = 1`, and the
`k` writes of the sorted indices. -/
def sort (k : ℕ) : Cost := ⟨k * (Nat.log 2 k + 1)⟩

/-- Sorting more keys costs more, which is what lets a bound on an operand's
size bound the cost of sorting it. -/
theorem sort_mono {k k' : ℕ} (h : k ≤ k') : sort k ≤ sort k' :=
  Nat.mul_le_mul h (Nat.succ_le_succ (Nat.log_mono_right h))

/-- The sort is at most `k * (k + 1)`, since `Nat.log 2 k ≤ k`. A caller reading
an asymptotic bound off a cost goes through this rather than the definition, so
tightening the model again stops at this file. -/
theorem sort_le_mul_succ (k : ℕ) : (sort k).ops ≤ k * (k + 1) :=
  Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.log_le_self 2 k))

/-- Closes a goal `f x ≤ f y` between costs by unfolding the named definitions to their `ops`
and comparing term by term, so each monotonicity theorem is one line. -/
syntax "cost_mono " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| cost_mono [$ds,*]) =>
    `(tactic| (simp only [$ds,*, Cost.le_iff, Cost.ops_add, Cost.ops_smul, Cost.matVec]; gcongr))

end Cost

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

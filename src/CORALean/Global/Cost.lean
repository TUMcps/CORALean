module

public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# What running an operation costs

A `Cost` counts **scalar operations**: one `+`, `-`, `*`, `/`, comparison,
`min`, `max` or absolute value on the scalar a layer computes in, at unit
price. Indexing, copying a generator block and allocating are free — which is
why `Zonotope.plusCost` never mentions the operands' generator counts, and why
a caller bound by data movement needs a model other than this one.

A cost is **asserted**, never derived. A Lean `def` says what an operation
computes and never what computing it costs, so every `…Cost` under a `Cost/`
directory is a `def` read off an operation's definition by hand, and is exactly
as trustworthy as that reading. Nothing here is `rfl` against an operation;
that is `Complexity/`'s job, for sizes, which are the other kind of claim.

Every cost is an **upper** bound, so bounds compose: a sequence costs at most
the sum of its steps, at any bound on each step's input. No enclosure guarantee
mentions a `Cost`, so a count read wrong makes a bound wrong, never a set.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
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

/-- One matrix-vector product `M *ᵥ v` at `m × n`: `m * n` multiplications and
`m * (n - 1)` additions, rounded up to `2 * m * n`. -/
def matVec (m n : ℕ) : Cost := ⟨2 * (m * n)⟩

/-- A comparison sort on `k` keys, at `k * (log₂ k + 1)`: the merge sort behind
`Tuple.sort` does at most `k * ⌈log₂ k⌉`, and `Nat.log 2` floors, so the `+ 1`
covers the ceiling and keeps `k = 0` and `k = 1` bounded. -/
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

end Cost

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.GCongr

@[expose] public section

/-!
# What running an operation costs

A `Cost` counts, at unit price, **scalar arithmetic** (one `+`, `-`, `*`, `/`, comparison, `min`,
`max` or absolute value) and **writes** (one unit for every scalar of the result, computed, copied
or padded, exponents and constraint coefficients included). **A computed entry costs its arithmetic
plus one write, a copied or padded entry one write**; reading is free, and a called subroutine is
charged its own cost, so a result is not charged again by its caller (`Zonotope.plusCost` takes the
operands' generator counts). A cost is **asserted**, never derived, read off an operation's
definition by hand, and an **upper** bound, so bounds compose. No enclosure guarantee mentions a
`Cost`: a count read wrong makes a bound wrong, never a set.
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

/-- The cost of no operations. -/
instance : Zero Cost := ⟨⟨0⟩⟩
/-- Costs add by their operation counts. -/
instance : Add Cost := ⟨fun a b => ⟨a.ops + b.ops⟩⟩
/-- A cost repeated `k` times. -/
instance : SMul ℕ Cost := ⟨fun k a => ⟨k * a.ops⟩⟩

-- `ops` is the whole content of a `Cost`, so the order lifts through it.
/-- Costs are ordered by their operation counts. -/
instance : Preorder Cost := Preorder.lift Cost.ops

/-- The zero cost counts no operations. -/
@[simp] theorem ops_zero : (0 : Cost).ops = 0 := rfl

/-- The operation count of a sum of costs is the sum of the counts. -/
@[simp] theorem ops_add (a b : Cost) : (a + b).ops = a.ops + b.ops := rfl

/-- The operation count of a repeated cost is `k` times its count. -/
@[simp] theorem ops_smul (k : ℕ) (a : Cost) : (k • a).ops = k * a.ops := rfl

/-- A cost is at most another exactly when its operation count is. -/
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


/-- Closes a goal `f x ≤ f y` between costs by unfolding the named definitions to their `ops`
and comparing term by term, so each monotonicity theorem is one line. -/
syntax "cost_mono " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| cost_mono [$ds,*]) =>
    `(tactic| (simp only [$ds,*, Cost.le_iff, Cost.ops_add, Cost.ops_smul, Cost.matVec]; gcongr))

end Cost

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

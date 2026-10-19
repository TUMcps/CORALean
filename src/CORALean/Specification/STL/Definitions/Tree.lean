module

public import CORALean.Specification.STL.Definitions.Cmp
public import CORALean.Specification.STL.Definitions.Expr
public import CORALean.Specification.STL.Definitions.Shift

@[expose] public section

/-!
# CORA's `stl` syntax tree and its semantics

The logic formulas of CORA's `stl` class (`@stl/stl.m`): the node types `true`, `false`, a
comparison of two expressions, `~`, `&`, `|`, `until`, `release`, `finally`, `globally` and
`next`. `implies` is no node (CORA builds `~φ | ψ`). Time bounds are closed intervals `[a,b]` of
`ℝ≥0`; an `stlInterval` with open ends is not modelled.

`ξ ⊨ₜ φ` reads each node as `modelCheckTrace.m` does. Its `aux_until` marks a time `t` when the
first witness `w` of `ψ` in the window comes before the first time `φ` fails from `t` on, so `φ
U[a,b] ψ` needs `φ` at every step from `t` up to and including the witness. This is not the strict
reading of `STL.Formula.Sat` (`φ` on `[0,t)`, the Roehm et al. semantics): the two semantics
differ, and no theorem relates `Tree.Sat` to `Formula.Sat`. `release` is `~until(~φ,~ψ)`,
`globally` is `~until(true,~φ)` and `finally` is `until(true,φ)`, written out.

Not modelled: the finite sampled traces of `modelCheckTrace`, whose `release` is false where the
window `[a,b]` outruns the trace (`ind = find(t >= obj.to,1)`); traces here are defined for all
time.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

inductive STL.Tree (n : ℕ)
  | tt
  | ff
  | cmp (op : STL.Cmp) (e₁ e₂ : STL.Expr n)
  | not (φ : Tree n)
  | and (φ ψ : Tree n)
  | or (φ ψ : Tree n)
  | until (a b : ℝ≥0) (φ ψ : Tree n)
  | release (a b : ℝ≥0) (φ ψ : Tree n)
  | finally (a b : ℝ≥0) (φ : Tree n)
  | globally (a b : ℝ≥0) (φ : Tree n)
  | next (a : ℝ≥0) (φ : Tree n)

/-- `ξ ⊨ₜ φ`, the trace `ξ : ℝ≥0 → ℝⁿ` satisfies the formula. -/
noncomputable def STL.Tree.Sat : STL.Tree n → (ℝ≥0 → Fin n → ℝ) → Prop
  | .tt, _ => True
  | .ff, _ => False
  | .cmp op e₁ e₂, ξ => op.rel (e₁.eval (ξ 0)) (e₂.eval (ξ 0))
  | .not φ, ξ => ¬ φ.Sat ξ
  | .and φ ψ, ξ => φ.Sat ξ ∧ ψ.Sat ξ
  | .or φ ψ, ξ => φ.Sat ξ ∨ ψ.Sat ξ
  | .until a b φ ψ, ξ =>
      ∃ t, a ≤ t ∧ t ≤ b ∧ ψ.Sat (Time.shift ξ t) ∧ ∀ t' ≤ t, φ.Sat (Time.shift ξ t')
  | .release a b φ ψ, ξ =>
      ¬ ∃ t, a ≤ t ∧ t ≤ b ∧ ¬ ψ.Sat (Time.shift ξ t) ∧ ∀ t' ≤ t, ¬ φ.Sat (Time.shift ξ t')
  | .finally a b φ, ξ => ∃ t, a ≤ t ∧ t ≤ b ∧ φ.Sat (Time.shift ξ t)
  | .globally a b φ, ξ => ∀ t, a ≤ t → t ≤ b → φ.Sat (Time.shift ξ t)
  | .next a φ, ξ => φ.Sat (Time.shift ξ a)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.STL.Definitions.Cmp
public import CORALean.Specification.STL.Definitions.Expr
public import CORALean.Specification.STL.Definitions.Shift

@[expose] public section

/-!
# CORA's `stl` syntax tree and its semantics

The logic formulas of CORA's `stl` class (`@stl/stl.m`): `true`, `false`, a comparison of two
expressions, `~`, `&`, `|`, `until`, `release`, `finally`, `globally` and `next`; `implies` is no
node. Time bounds are closed intervals `[a,b]` of `ℝ≥0`. `ξ ⊨ₜ φ` reads each node as
`modelCheckTrace.m` does; `Tree.HasUntilWitness` writes the window once: `φ U[a,b] ψ`
needs `φ` at every step up to and including the witness, not `[0,t)` as `STL.Formula.Sat` (Roehm
et al.); no theorem relates the two. Not modelled: the finite sampled traces of `modelCheckTrace`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


variable {n : ℕ} {X : Type}


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

/-- `P U[a,b] Q` holds of `ξ`: `Q` at a time `t ∈ [a,b]` and `P` at every step up to
and including `t`. -/
def STL.Tree.HasUntilWitness (a b : ℝ≥0) (P Q : (ℝ≥0 → X) → Prop) (ξ : ℝ≥0 → X) :
    Prop :=
  ∃ t, a ≤ t ∧ t ≤ b ∧ Q (Time.shift ξ t) ∧ ∀ t' ≤ t, P (Time.shift ξ t')

/-- `ξ ⊨ₜ φ`, the trace `ξ : ℝ≥0 → ℝⁿ` satisfies the formula. -/
noncomputable def STL.Tree.Sat : STL.Tree n → (ℝ≥0 → Fin n → ℝ) → Prop
  | .tt, _ => True
  | .ff, _ => False
  | .cmp op e₁ e₂, ξ => op.rel (e₁.eval (ξ 0)) (e₂.eval (ξ 0))
  | .not φ, ξ => ¬ φ.Sat ξ
  | .and φ ψ, ξ => φ.Sat ξ ∧ ψ.Sat ξ
  | .or φ ψ, ξ => φ.Sat ξ ∨ ψ.Sat ξ
  | .until a b φ ψ, ξ => HasUntilWitness a b φ.Sat ψ.Sat ξ
  | .release a b φ ψ, ξ => ¬ HasUntilWitness a b (fun ζ => ¬ φ.Sat ζ) (fun ζ => ¬ ψ.Sat ζ) ξ
  | .finally a b φ, ξ => HasUntilWitness a b (fun _ => True) φ.Sat ξ
  | .globally a b φ, ξ => ¬ HasUntilWitness a b (fun _ => True) (fun ζ => ¬ φ.Sat ζ) ξ
  | .next a φ, ξ => φ.Sat (Time.shift ξ a)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

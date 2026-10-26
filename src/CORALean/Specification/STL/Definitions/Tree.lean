module

public import CORALean.Specification.STL.Definitions.Cmp
public import CORALean.Specification.STL.Definitions.Expr
public import CORALean.Specification.STL.Definitions.Shift

@[expose] public section

/-!
# CORA's `stl` syntax tree and its semantics

The logic formulas of CORA's `stl` class (`@stl/stl.m`): `true`, `false`, a comparison of two
expressions, `~`, `&`, `|`, `until`, `release`, `finally`, `globally` and `next`; `implies` is no
node. Time bounds are closed intervals `[a,b]`, of `ℝ≥0` in the semantics; the tree is generic over
the types of the bounds and of the numbers (`STL.Tree 𝕋 𝕋 n` at a float scalar). `ξ ⊨ₜ φ` reads
each node as `modelCheckTrace.m` does; `Tree.HasUntilWitness` writes the window once: `φ U[a,b] ψ`
needs `φ` at every step up to and including the witness, not `[0,t)` as `STL.Formula.Satisfies`
(Roehm et al.); no theorem relates the two. Not modelled: the sampled traces of `modelCheckTrace`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


variable {n : ℕ} {X : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- CORA's `stl` syntax tree: true, false, comparison of two expressions, negation, conjunction,
disjunction, until, release, finally, globally and next, with closed time bounds. -/
inductive STL.Tree (τ κ : Type) (n : ℕ)
  | tt
  | ff
  | cmp (op : STL.Cmp) (e₁ e₂ : STL.Expr κ n)
  | not (φ : Tree τ κ n)
  | and (φ ψ : Tree τ κ n)
  | or (φ ψ : Tree τ κ n)
  | until (a b : τ) (φ ψ : Tree τ κ n)
  | release (a b : τ) (φ ψ : Tree τ κ n)
  | finally (a b : τ) (φ : Tree τ κ n)
  | globally (a b : τ) (φ : Tree τ κ n)
  | next (a : τ) (φ : Tree τ κ n)

/-- `P U[a,b] Q` holds of `ξ`: `Q` at a time `t ∈ [a,b]` and `P` at every step up to
and including `t`. -/
def STL.Tree.HasUntilWitness (a b : ℝ≥0) (P Q : (ℝ≥0 → X) → Prop) (ξ : ℝ≥0 → X) :
    Prop :=
  ∃ t, a ≤ t ∧ t ≤ b ∧ Q (Time.shift ξ t) ∧ ∀ t' ≤ t, P (Time.shift ξ t')

/-- `ξ ⊨ₜ φ`, the trace `ξ : ℝ≥0 → ℝⁿ` satisfies the formula. -/
noncomputable def STL.Tree.Satisfies : STL.Tree ℝ≥0 ℝ n → (ℝ≥0 → Fin n → ℝ) → Prop
  | .tt, _ => True
  | .ff, _ => False
  | .cmp op e₁ e₂, ξ => op.Relates (e₁.eval (ξ 0)) (e₂.eval (ξ 0))
  | .not φ, ξ => ¬ φ.Satisfies ξ
  | .and φ ψ, ξ => φ.Satisfies ξ ∧ ψ.Satisfies ξ
  | .or φ ψ, ξ => φ.Satisfies ξ ∨ ψ.Satisfies ξ
  | .until a b φ ψ, ξ => HasUntilWitness a b φ.Satisfies ψ.Satisfies ξ
  | .release a b φ ψ, ξ => ¬ HasUntilWitness a b (fun ζ => ¬ φ.Satisfies ζ) (fun ζ => ¬ ψ.Satisfies
      ζ) ξ
  | .finally a b φ, ξ => HasUntilWitness a b (fun _ => True) φ.Satisfies ξ
  | .globally a b φ, ξ => ¬ HasUntilWitness a b (fun _ => True) (fun ζ => ¬ φ.Satisfies ζ) ξ
  | .next a φ, ξ => φ.Satisfies (Time.shift ξ a)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

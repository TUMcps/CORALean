module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# Eliminating `true` and `false`, with one rewrite a parameter

`@stl/eliminateTrueFalse.m`: simplifies a formula bottom-up, where a sub-formula is `true` or
`false`. Each case is one `if` chain of CORA's, written as a `match` on the simplified operands in
the same order. One case rewrites a node on a constant operand and is a parameter: `ut a b φ`
replaces `φ U[a,b] true`. CORA's is `true` (`eliminateTrueFalseCora`), which is not equivalent
(`eliminateTrueFalse` keeps the node).

Real-only, a specification: it rewrites or builds formulas, whose time bounds and constants are
part of the syntax and are copied or added exactly, never rounded.

## Inputs
* `ut` – rewrite of an until with true

## Output
* the formula without true and false
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


variable {τ κ : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `eliminateTrueFalse(obj)`, with `ut` the rewrite of `φ U[a,b] true`. -/
def STL.Tree.eliminateTrueFalseWith (ut : τ → τ → STL.Tree τ κ n → STL.Tree τ κ n) :
    STL.Tree τ κ n → STL.Tree τ κ n
  | .tt => .tt
  | .ff => .ff
  | .cmp op e₁ e₂ => .cmp op e₁ e₂
  -- `&`: `false` absorbs, `true` is dropped
  | .and φ ψ =>
      let lhs := eliminateTrueFalseWith ut φ
      let rhs := eliminateTrueFalseWith ut ψ
      match lhs, rhs with
      | .ff, _ => .ff
      | _, .ff => .ff
      | .tt, _ => rhs
      | _, .tt => lhs
      | _, _ => .and lhs rhs
  -- `|`: `true` absorbs, `false` is dropped
  | .or φ ψ =>
      let lhs := eliminateTrueFalseWith ut φ
      let rhs := eliminateTrueFalseWith ut ψ
      match lhs, rhs with
      | .tt, _ => .tt
      | _, .tt => .tt
      | .ff, _ => rhs
      | _, .ff => lhs
      | _, _ => .or lhs rhs
  -- `~`: `true` and `false` swap
  | .not φ =>
      let inner := eliminateTrueFalseWith ut φ
      match inner with
      | .ff => .tt
      | .tt => .ff
      | _ => .not inner
  | .next a φ =>
      let inner := eliminateTrueFalseWith ut φ
      match inner with
      | .ff => .ff
      | .tt => .tt
      | _ => .next a inner
  -- `until`: a `true` left operand makes it `finally`, a constant right operand decides it
  | .until a b φ ψ =>
      let lhs := eliminateTrueFalseWith ut φ
      let rhs := eliminateTrueFalseWith ut ψ
      match lhs, rhs with
      | .tt, _ => .finally a b rhs
      | _, .tt => ut a b lhs
      | _, .ff => .ff
      | _, _ => .until a b lhs rhs
  -- `release`: a `false` left operand makes it `globally`, a constant operand decides it
  | .release a b φ ψ =>
      let lhs := eliminateTrueFalseWith ut φ
      let rhs := eliminateTrueFalseWith ut ψ
      match lhs, rhs with
      | .ff, _ => .globally a b rhs
      | _, .tt => .tt
      | .tt, _ => .tt
      | _, _ => .release a b lhs rhs
  -- `finally`, `globally`, `next`: a constant operand decides them
  | .finally a b φ =>
      let inner := eliminateTrueFalseWith ut φ
      match inner with
      | .ff => .ff
      | .tt => .tt
      | _ => .finally a b inner
  | .globally a b φ =>
      let inner := eliminateTrueFalseWith ut φ
      match inner with
      | .ff => .ff
      | .tt => .tt
      | _ => .globally a b inner

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

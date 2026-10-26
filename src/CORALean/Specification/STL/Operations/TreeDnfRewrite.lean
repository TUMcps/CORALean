module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# One pass of the disjunctive-normal-form rewrite

`@stl/disjunctiveNormalForm.m`, `aux_rewrite(obj)`: bottom-up, an `&` with an `|` operand is
distributed over it, and the number of distributions is counted. Both operands `|`: four cubes;
the left one `|`: two; the right one `|`: two, decided on the operand of `obj` (`obj.rhs.type`),
not on the rewritten one, as printed (the rewritten one is an `|` whenever the original is, so
the two agree; an operand that only becomes an `|` is left for the next pass). Every other node
(a comparison, `~`, a temporal operator) is a leaf and is not entered.

## Inputs
* none

## Output
* the formula after one rewrite pass and the number of changes
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

/-- `[res,cnt] = aux_rewrite(obj)` of `disjunctiveNormalForm.m`. -/
def STL.Tree.dnfRewrite : STL.Tree τ κ n → STL.Tree τ κ n × ℕ
  | .and φ ψ =>
    let lhs := (dnfRewrite φ).1
    let rhs := (dnfRewrite ψ).1
    let cnt := (dnfRewrite φ).2 + (dnfRewrite ψ).2
    match lhs, rhs, ψ with
    | .or l₁ l₂, .or r₁ r₂, _ =>
      (.or (.or (.or (.and l₁ r₁) (.and l₁ r₂)) (.and l₂ r₁)) (.and l₂ r₂), cnt + 1)
    | .or l₁ l₂, _, _ => (.or (.and rhs l₁) (.and rhs l₂), cnt + 1)
    | _, .or r₁ r₂, .or _ _ => (.or (.and lhs r₁) (.and lhs r₂), cnt + 1)
    | _, _, _ => (.and lhs rhs, cnt)
  | .or φ ψ => (.or (dnfRewrite φ).1 (dnfRewrite ψ).1, (dnfRewrite φ).2 + (dnfRewrite ψ).2)
  | φ => (φ, 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

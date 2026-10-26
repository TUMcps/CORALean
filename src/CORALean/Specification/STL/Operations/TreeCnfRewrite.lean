module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# One pass of the conjunctive-normal-form rewrite

`@stl/conjunctiveNormalForm.m`, `aux_rewrite(obj)`: bottom-up, an `|` with an `&` operand is
distributed over it, and the number of distributions is counted. Both operands `&`: four clauses;
the left one `&`: two; the right one `&`: two, decided on the operand of `obj` (`obj.rhs.type`),
not on the rewritten one, as printed (the rewritten one is an `&` whenever the original is, so
the two agree; an operand that only becomes an `&` is left for the next pass). Every other node
(a comparison, `~`, a temporal operator) is a leaf and is not entered.

## Inputs
* none

## Output
* the formula after one rewrite pass and the number of changes
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {τ κ : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[res,cnt] = aux_rewrite(obj)` of `conjunctiveNormalForm.m`. -/
def STL.Tree.cnfRewrite : STL.Tree τ κ n → STL.Tree τ κ n × ℕ
  | .or φ ψ =>
    let lhs := (cnfRewrite φ).1
    let rhs := (cnfRewrite ψ).1
    let cnt := (cnfRewrite φ).2 + (cnfRewrite ψ).2
    match lhs, rhs, ψ with
    | .and l₁ l₂, .and r₁ r₂, _ =>
      (.and (.and (.and (.or l₁ r₁) (.or l₁ r₂)) (.or l₂ r₁)) (.or l₂ r₂), cnt + 1)
    | .and l₁ l₂, _, _ => (.and (.or rhs l₁) (.or rhs l₂), cnt + 1)
    | _, .and r₁ r₂, .and _ _ => (.and (.or lhs r₁) (.or lhs r₂), cnt + 1)
    | _, _, _ => (.or lhs rhs, cnt)
  | .and φ ψ => (.and (cnfRewrite φ).1 (cnfRewrite ψ).1, (cnfRewrite φ).2 + (cnfRewrite ψ).2)
  | φ => (φ, 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

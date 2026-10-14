module

public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.Specification.STL.Operations.CmpDual

@[expose] public section

/-!
# The predicate node of a comparison

`@stl/lt.m`, `le.m`, `gt.m` and `ge.m` build the node the same way and differ in the operator:
with a number on the right the node compares the `stl` operand with it, with a number on the left
the operands are swapped (`5 < x` is `x > 5`), and two `stl` operands are compared by their
difference with `0`. Two numbers never reach the method in CORA (MATLAB compares them), and here
give the comparison of the two.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The node of `e₁ op e₂`, `op` one of `<`, `<=`, `>`, `>=`. -/
def STL.Tree.compare (op : STL.Cmp) (e₁ e₂ : STL.Expr n) : STL.Tree n :=
  match e₁, e₂ with
  | _, .num _ => .cmp op e₁ e₂
  | .num _, _ => .cmp op.dual e₂ e₁
  | _, _ => .cmp op (.sub e₁ e₂) (.num 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

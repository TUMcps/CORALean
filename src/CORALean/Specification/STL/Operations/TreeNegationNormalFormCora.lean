module

public import CORALean.Specification.STL.Operations.TreeNnfWith
public import CORALean.Specification.STL.Operations.CmpDual

@[expose] public section

/-!
# CORA's `negationNormalForm`, as printed

`@stl/negationNormalForm.m` turns `~(x < 5)` into `x > 5` (`obj.lhs > obj.rhs`), `~(x > 5)` into
`x < 5`, `~(x <= 5)` into `x >= 5` and `~(x >= 5)` into `x <= 5`: the sides swap and the
strictness stays, so the result differs from the formula at the boundary (`x = 5`). The result is
not equivalent to the argument; `STL.Tree.negationNormalFormCora_counterexample` is a trace where
it differs, and `STL.Tree.negationNormalForm` the version with `Cmp.negate`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `negationNormalForm(obj)`, `aux_recursive(obj,false)`, as printed. -/
def STL.Tree.negationNormalFormCora (φ : STL.Tree n) : STL.Tree n :=
  STL.Tree.nnfWith STL.Cmp.dual false φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

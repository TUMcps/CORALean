module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# Removing the syntactic sugar

`@stl/desugar.m`: the result has only `until`, `&`, `|` and `~` (and the comparisons, `true` and
`false`). `release` becomes `~until(~φ,~ψ)`, `finally` `until(true,φ)`, `globally`
`~until(true,~φ)` and `next` `until(true,φ)` on `[a,a]`. CORA desugars the rewritten formula again
(`desugar(~until(~φ,~ψ))`); the recursion here is that call unfolded, since `desugar(~χ)` is
`~desugar(χ)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `desugar(phi)` of `desugar.m`. -/
def STL.Tree.desugar : STL.Tree n → STL.Tree n
  | .tt => .tt
  | .ff => .ff
  | .cmp op e₁ e₂ => .cmp op e₁ e₂
  | .not φ => .not (desugar φ)
  | .and φ ψ => .and (desugar φ) (desugar ψ)
  | .or φ ψ => .or (desugar φ) (desugar ψ)
  | .until a b φ ψ => .until a b (desugar φ) (desugar ψ)
  | .release a b φ ψ => .not (.until a b (.not (desugar φ)) (.not (desugar ψ)))
  | .finally a b φ => .until a b .tt (desugar φ)
  | .globally a b φ => .not (.until a b .tt (.not (desugar φ)))
  | .next a φ => .until a a .tt (desugar φ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

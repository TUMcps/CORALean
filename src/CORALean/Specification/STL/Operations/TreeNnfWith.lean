module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# Negation normal form, with the negation of a comparison a parameter

`@stl/negationNormalForm.m`, `aux_recursive(obj,neg)`: pushes `~` to the comparisons, `neg` saying
whether the sub-formula is under an odd number of them. `&` and `|`, `finally` and `globally`,
`until` and `release` swap under `neg`, `next` and `~` stay or vanish, `true` and `false` swap,
and a comparison becomes `ng` of itself. CORA's `ng` is `Cmp.dual` (`negationNormalFormCora`), the
negation is `Cmp.negate` (`negationNormalForm`).

## Inputs
* `ng` – negation of a comparison

## Output
* the formula in negation normal form
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

/-- `aux_recursive(obj,neg)` of `negationNormalForm.m`. -/
def STL.Tree.nnfWith (ng : STL.Cmp → STL.Cmp) : Bool → STL.Tree τ κ n → STL.Tree τ κ n
  | true, .and φ ψ => .or (nnfWith ng true φ) (nnfWith ng true ψ)
  | true, .or φ ψ => .and (nnfWith ng true φ) (nnfWith ng true ψ)
  | true, .not φ => nnfWith ng false φ
  | true, .finally a b φ => .globally a b (nnfWith ng true φ)
  | true, .globally a b φ => .finally a b (nnfWith ng true φ)
  | true, .until a b φ ψ => .release a b (nnfWith ng true φ) (nnfWith ng true ψ)
  | true, .release a b φ ψ => .until a b (nnfWith ng true φ) (nnfWith ng true ψ)
  | true, .next a φ => .next a (nnfWith ng true φ)
  | true, .cmp op e₁ e₂ => .cmp (ng op) e₁ e₂
  | true, .tt => .ff
  | true, .ff => .tt
  | false, .and φ ψ => .and (nnfWith ng false φ) (nnfWith ng false ψ)
  | false, .or φ ψ => .or (nnfWith ng false φ) (nnfWith ng false ψ)
  | false, .not φ => nnfWith ng true φ
  | false, .finally a b φ => .finally a b (nnfWith ng false φ)
  | false, .globally a b φ => .globally a b (nnfWith ng false φ)
  | false, .until a b φ ψ => .until a b (nnfWith ng false φ) (nnfWith ng false ψ)
  | false, .release a b φ ψ => .release a b (nnfWith ng false φ) (nnfWith ng false ψ)
  | false, .next a φ => .next a (nnfWith ng false φ)
  | false, φ => φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

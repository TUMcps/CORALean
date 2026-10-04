import Mathlib.Order.Basic

/-!
# Propositional formulas

`ϱ := p | ¬ϱ | ϱ₁ ∨ ϱ₂`, the non-temporal part both [1, Def. 1] (RTL) and [1, Sec. 2.2] (STL)
are built over, and `r ⊨ₚ ϱ` of [1, Def. 2].

An atomic predicate is a predicate `X → Prop` itself, in place of a name `p ∈ AP` and an
evaluation function `π_p`: a finite `AP` and its `π` are one such predicate each.
`top`, `bot`, `and` and `bigOr` are the abbreviations the later rows use.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- ========================================  MAIN TYPE  ========================================= --

inductive Pform (X : Type)
  | atom (p : X → Prop)
  | not (ϱ : Pform X)
  | or (ϱ₁ ϱ₂ : Pform X)

/-- `r ⊨ₚ ϱ`, [1, Def. 2]. -/
def Pform.Sat : Pform X → X → Prop
  | .atom p, r => p r
  | .not ϱ, r => ¬ ϱ.Sat r
  | .or ϱ₁ ϱ₂, r => ϱ₁.Sat r ∨ ϱ₂.Sat r

/-- The predicate that always holds. -/
abbrev Pform.top : Pform X := .atom fun _ => True

/-- The predicate that never holds. -/
abbrev Pform.bot : Pform X := .atom fun _ => False

/-- Conjunction, by De Morgan. -/
abbrev Pform.and (ϱ₁ ϱ₂ : Pform X) : Pform X := .not (.or (.not ϱ₁) (.not ϱ₂))

/-- `⋁` of a list, `⊥` for the empty one. -/
abbrev Pform.bigOr (L : List (Pform X)) : Pform X := L.foldr Pform.or Pform.bot

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

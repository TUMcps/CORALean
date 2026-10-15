module

public import CORALean.Specification.Kleene.Kleene
public import Mathlib.Order.Nat

@[expose] public section

/-!
# The truth order of Kleene's three values

`⊥ ⊑ₜ ⊣₁ ⊑ₜ ⊤` of [1, Sec. 2.2 (order)] is the order of the stored codes `False(0) < Unknown(1) <
True(2)` (`Kleene.le_iff_code`), a linear order: on the three values `&` is its minimum and `|` its
maximum (`Kleene.code_and`, `Kleene.code_or`).

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  INSTANCES  ========================================= --

/-- `⊥ ⊑ₜ ⊣₁ ⊑ₜ ⊤`: the order of the stored codes. -/
instance : LinearOrder Kleene :=
  LinearOrder.lift' Kleene.code (by intro a b h; cases a <;> cases b <;> simp_all [Kleene.code])

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

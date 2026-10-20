module

public import CORALean.Specification.Rtl.Rtl
public import CORALean.Specification.STL.Definitions.RTL

@[expose] public section

/-!
# An `rtl` object as a formula of the paper

The `rtl` tree is the fragment `Aϱ | ψ₁ ∧ ψ₂ | ψ₁ ∨ ψ₂ | Xₐψ` of [1, Def. 1]; `f` reads a leaf as
the propositional formula `ϱ` it holds. The shift `a` of `Xₐ` is a nonnegative real in the paper;
`next` of CORA accepts every multiple of `0.5`, negative ones too, which have no counterpart, and
`toFormula` is `none` for them.

## Inputs
* `f` – reading of a label as a predicate

## Output
* the paper's RTL formula, or none for a negative time shift

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {L X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The formula of [1, Def. 1] that an `rtl` object is. -/
noncomputable def Rtl.toFormula (f : L → Pform X) : Rtl L → Option (RTL.Formula X)
  | .all l => some (.A (f l))
  | .and a b => (a.toFormula f).bind fun a' => (b.toFormula f).map (RTL.Formula.and a')
  | .or a b => (a.toFormula f).bind fun a' => (b.toFormula f).map (RTL.Formula.or a')
  | .next t a => if 0 ≤ t then (a.toFormula f).map (RTL.Formula.next t.toNNReal) else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

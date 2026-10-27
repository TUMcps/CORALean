module

public import CORALean.Specification.Rtl.Rtl
public import CORALean.Specification.STL.Definitions.Shift
public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# The semantics of an RTL formula

`R ⊨ᵣ ψ` of [1, Def. 2], Eqs. (4)-(7), for a reach sequence `R : ℝ≥0 → Set X` of sets of states.
A leaf `Aϱ` holds if `ϱ` holds of all states of `R(0)`; `sat l r` says that state `r` satisfies the
leaf `l`. A negative shift of `next` is read as `0` (`Real.toNNReal`); `next` rejects no negative
time, see `Rtl.toFormula`.

## Inputs
* `sat` – satisfaction of a label by a state

## Output
* the satisfaction relation of formulas on reach sequences

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {L X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R ⊨ᵣ ψ`. -/
def Rtl.Satisfies (sat : L → X → Prop) : Rtl ℝ L → (ℝ≥0 → Set X) → Prop
  | .all l, R => ∀ r ∈ R 0, sat l r
  | .and a b, R => a.Satisfies sat R ∧ b.Satisfies sat R
  | .or a b, R => a.Satisfies sat R ∨ b.Satisfies sat R
  | .next t a, R => a.Satisfies sat (Time.shift R t.toNNReal)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.ReachSetAnalyzer.Definitions.Entry
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Reach sets whose time intervals enclose others

`R` has enclosing times for `Rx` when both list the same number of entries and each entry of `Rx`
has the location of the entry of `R` at its index and only sets that one lists too, each in a time
interval the one of `R` encloses: the float reach sets, read as reals, enclose the exact ones.

## Inputs
* `R` – enclosing reach sets
* `Rx` – enclosed reach sets

## Output
* the time intervals of `R` enclose those of `Rx`, set by set
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The time intervals of `R` enclose those of `Rx`, entry by entry and set by set. -/
def ReachSetAnalyzer.HasEnclosingTimes (R Rx : List (ReachSetAnalyzer.Entry ℝ S n)) : Prop :=
  R.length = Rx.length ∧ ∀ (i : ℕ) (e ex : ReachSetAnalyzer.Entry ℝ S n), R[i]? = some e →
    Rx[i]? = some ex → ex.loc = e.loc ∧ ∀ stx ∈ ex.timeInterval, ∃ st ∈ e.timeInterval,
      st.set = stx.set ∧ st.time.inf ≤ stx.time.inf ∧ stx.time.sup ≤ st.time.sup

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

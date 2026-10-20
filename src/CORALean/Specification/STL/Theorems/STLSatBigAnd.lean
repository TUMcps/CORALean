module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatAnd

@[expose] public section

/-!
# A conjunction of STL formulas

`ξ ⊨ₜ ⋀ (l.map g) ⇔ ∀ b ∈ l, ξ ⊨ₜ g b`, the `⋀ᵢ` of [1, Sec. 4.1].

## Inputs
* `β` – index type
* `l` – list of indices
* `g` – formula of each index
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the conjunction holds iff every formula holds

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Formula.sat_bigAnd {β : Type} (l : List β) (g : β → STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.bigAnd (l.map g)).Sat ξ ↔ ∀ b ∈ l, (g b).Sat ξ := by -- --- PROOF ---
  induction l with
  | nil => simp [STL.Formula.bigAnd, STL.Formula.tt, STL.Formula.Sat]
  | cons b l ih =>
    -- one step of the fold is a binary `∧`
    have : (STL.Formula.bigAnd ((b :: l).map g)).Sat ξ ↔
        (g b).Sat ξ ∧ (STL.Formula.bigAnd (l.map g)).Sat ξ := STL.Formula.sat_and _ _ _
    rw [this, ih]
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

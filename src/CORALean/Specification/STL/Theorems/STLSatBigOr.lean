module

public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# A disjunction of STL formulas

`ξ ⊨ₜ ⋁ (l.map g) ⇔ ∃ b ∈ l, ξ ⊨ₜ g b`, the `⋁ⱼ` and `⋁_k` of [1, Sec. 4.1].

## Inputs
* `β` – index type
* `l` – list of indices
* `g` – formula of each index
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the disjunction holds iff some formula holds

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Formula.sat_bigOr {β : Type} (l : List β) (g : β → STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.bigOr (l.map g)).Sat ξ ↔ ∃ b ∈ l, (g b).Sat ξ := by -- --- PROOF ---
  induction l with
  | nil => simp [STL.Formula.bigOr, STL.Formula.ff, STL.Formula.Sat]
  | cons b l ih =>
    -- one step of the fold is a binary `∨`
    have : (STL.Formula.bigOr ((b :: l).map g)).Sat ξ ↔
        (g b).Sat ξ ∨ (STL.Formula.bigOr (l.map g)).Sat ξ := Iff.rfl
    rw [this, ih]
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

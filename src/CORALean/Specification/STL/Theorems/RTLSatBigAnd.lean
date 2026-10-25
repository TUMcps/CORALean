module

public import CORALean.Specification.STL.Operations.RTLBigAnd

@[expose] public section

/-!
# A conjunction of RTL formulas

`R ⊨ᵣ ⋀ (l.map g) ⇔ ∀ b ∈ l, R ⊨ᵣ g b`, the `⋀ᵢ` of [1, Lemma 2], Eq. (16).

## Inputs
* `β` – index type
* `l` – list of indices
* `g` – formula of each index
* `R` – reach sequence

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

theorem RTL.Formula.sat_bigAnd {β : Type} (l : List β) (g : β → RTL.Formula X)
    (R : ℝ≥0 → Set X) : -- --- CONCL ---
    (RTL.Formula.bigAnd (l.map g)).Satisfies R ↔ ∀ b ∈ l, (g b).Satisfies R := by -- --- PROOF ---
  induction l with
  | nil => simp [RTL.Formula.bigAnd, RTL.Formula.Satisfies, Pform.Satisfies]
  | cons b l ih =>
    have : (RTL.Formula.bigAnd ((b :: l).map g)).Satisfies R ↔
        (g b).Satisfies R ∧ (RTL.Formula.bigAnd (l.map g)).Satisfies R := Iff.rfl
    rw [this, ih]
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

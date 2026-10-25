module

public import CORALean.Specification.STL.Definitions.Pform

@[expose] public section

/-!
# A disjunction of predicates

`r ⊨ₚ ⋁ K ⇔ ∃ ϱ ∈ K, r ⊨ₚ ϱ`, the `ϱ' = ⋁_k ϱ_k` of [1, Lemma 2], Eq. (17).

## Inputs
* `K` – list of predicates
* `r` – state

## Hypotheses
* none

## Conclusion
* the disjunction holds at the state iff one predicate does

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Pform.sat_bigOr (K : List (Pform X)) (r : X) : -- --- CONCL ---
    (Pform.bigOr K).Satisfies r ↔ ∃ ϱ ∈ K, ϱ.Satisfies r := by -- --- PROOF ---
  induction K with
  | nil => simp [Pform.bigOr, Pform.Satisfies]
  | cons ϱ K ih =>
    -- one step of the fold is a binary `∨`
    have : (Pform.bigOr (ϱ :: K)).Satisfies r ↔ ϱ.Satisfies r ∨ (Pform.bigOr K).Satisfies r :=
        Iff.rfl
    rw [this, ih]
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.Data.List.Nodup
public import CORALean.Specification.STL.Operations.SampToCNF
public import CORALean.Specification.STL.Theorems.ClauseNodupMerge

@[expose] public section

/-!
# The normal form has distinct powers

[1, Sec. 4.1]: every clause of `s.toCNF` has one branch per `j`, as [1, Lemma 2] reads its normal
form.

## Inputs
* `s` – sampled time formula
* `pos` – positive polarity

## Hypotheses
* none

## Conclusion
* every clause of the normal form has distinct powers

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

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Samp.nodup_toCNF (s : STL.Samp X) (pos : Bool) :
    ∀ clause ∈ s.toCNF pos, (clause.map STL.Branch.j).Nodup := by -- --- PROOF ---
  -- the clauses of a disjunction are merges, those of a conjunction are the two lists'
  have hor : ∀ a b : STL.CNF X, (∀ clause ∈ a, (clause.map STL.Branch.j).Nodup) →
      ∀ clause ∈ a.or b, (clause.map STL.Branch.j).Nodup := by
    intro a b ha clause h
    obtain ⟨cl₁, h₁, cl₂, h₂, rfl⟩ := by simpa [STL.CNF.or] using h
    exact STL.Clause.nodup_merge cl₁ cl₂ (ha cl₁ h₁)
  induction s generalizing pos with
  | lit ϱ => cases pos <;> simp [STL.Samp.toCNF]
  | not s ih => exact ih (!pos)
  | and s t ihs iht =>
    cases pos
    · exact hor _ _ (ihs false)
    · intro clause h
      rcases List.mem_append.1 (by simpa [STL.Samp.toCNF] using h) with h | h
      · exact ihs true clause h
      · exact iht true clause h
  | or s t ihs iht =>
    -- the same, with the roles of the two cases swapped
    cases pos
    · intro clause h
      rcases List.mem_append.1 (by simpa [STL.Samp.toCNF] using h) with h | h
      · exact ihs false clause h
      · exact iht false clause h
    · exact hor _ _ (ihs true)
  | next s ih =>
    intro clause h
    -- a clause of the result is a clause of `s` with every `j` raised
    obtain ⟨cl, hcl, rfl⟩ := by simpa [STL.Samp.toCNF, STL.CNF.next] using h
    -- raising every `j` by one keeps them distinct
    have := List.Nodup.map (f := fun j : ℕ => j + 1) (fun a b h => by simpa using h)
      (ih pos cl hcl)
    simpa [Function.comp_def] using this
  | fin ϱ => cases pos <;> simp [STL.Samp.toCNF]
  | glob ϱ => cases pos <;> simp [STL.Samp.toCNF]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

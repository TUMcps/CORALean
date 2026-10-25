module

public import CORALean.Specification.STL.Definitions.ReachSequence
public import CORALean.Specification.STL.Definitions.Pform

@[expose] public section

/-!
# A predicate holds of every trace at a time iff it holds of the whole set

`(∀ ξ ∈ C(R), ϱ ⊨ₚ ξ(a)) ⇔ ∀ r ∈ R(a), r ⊨ₚ ϱ`: a trace passes through any state of `R(a)`, given a
state at every other time. How [1, Lemma 2]'s proof, and the example of [1, Sec. 3], read `A ϱ`.

## Inputs
* `R` – reach sequence
* `a` – time
* `ϱ` – predicate

## Hypotheses
* `hne` – all reach sets are nonempty

## Conclusion
* the predicate holds for every trace at the time iff for the whole set

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

theorem ReachSequence.forall_traceSet_sat_iff {R : ℝ≥0 → Set X} (hne : ∀ t, (R t).Nonempty)
    (a : ℝ≥0) (ϱ : Pform X) : -- --- CONCL ---
    (∀ ξ ∈ ReachSequence.traceSet R, ϱ.Satisfies (ξ a)) ↔ ∀ r ∈ R a, ϱ.Satisfies
    r := by -- --- PROOF ---
  classical
  refine ⟨fun h r hr => ?_, fun h ξ hξ => h _ (hξ a)⟩
  -- extend `r` to a trace of `C(R)`
  let ξ : ℝ≥0 → X := fun x => if x = a then r else (hne x).some
  have hξ : ξ ∈ ReachSequence.traceSet R := by
    intro x
    by_cases hx : x = a
    · subst hx; simpa [ξ] using hr
    · simpa [ξ, hx] using (hne x).some_mem
  simpa [ξ] using h ξ hξ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

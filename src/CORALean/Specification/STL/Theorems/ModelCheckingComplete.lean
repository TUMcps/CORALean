module

public import CORALean.Specification.STL.Theorems.SampSatToCNF
public import CORALean.Specification.STL.Theorems.SampNodupToCNF
public import CORALean.Specification.STL.Theorems.CNFUpsilonSoundComplete

@[expose] public section

/-!
# Model checking a sampled time formula is complete

[1, Thm. 1]: for a sampled time formula the transformation is also complete: `R ⊨ᵣ ψ ⇔ C(R) ⊨ₜ ϕ`,
by [1, Lemma 2] and the equivalence of the normal form. [1] says it for "`ϕ` equivalent to a
sampled time formula", which the rewriting of Table 1, only an implication, does not give; this is
the case of a sampled time `ϕ` itself.

## Inputs
* `c` – time step
* `s` – sampled time formula

## Hypotheses
* `hc` – the time step is positive

## Conclusion
* a normal form exists whose transformation is equivalent to the formula

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
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

theorem STL.model_checking_complete_sampled {c : ℝ≥0} (hc : 0 < c)
    (s : STL.Samp X) : -- --- CONCL ---
    ∃ cnf : STL.CNF X, (∀ clause ∈ cnf, (clause.map STL.Branch.j).Nodup) ∧
      ∀ (T : Finset ℝ≥0) (R : ℝ≥0 → Set X), (∀ t, (R t).Nonempty) →
        ReachSequence.IsFinRep T R → ReachSequence.IsCDivisible c T →
          ((cnf.upsilon c).Satisfies R ↔
            (s.toFormula c).HoldsOn (ReachSequence.traceSet R)) := by -- --- PROOF ---
  refine ⟨s.toCNF true, s.nodup_toCNF true, fun T R hne hT hT' => ?_⟩
  rw [STL.CNF.upsilon_sound_complete hc hne hT hT' (s.toCNF true) (s.nodup_toCNF true)]
  exact forall₂_congr fun ξ _ => by simpa using STL.Samp.sat_toCNF c s true ξ


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

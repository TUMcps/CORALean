module

public import CORALean.Specification.STL.Operations.RTLFinally
public import CORALean.Specification.STL.Theorems.ForallTraceSetSatIff
public import CORALean.Specification.STL.Theorems.SatOfPform

@[expose] public section

/-!
# What `F[0,1] Aϱ` says of the traces

[1, Sec. 3]: `R ⊨ᵣ F[0,1] Aϱ ⇔ ∃t ∈ [0,1]: C(R) ⊨ₜ F[t,t] ϱ ⇒ C(R) ⊨ₜ F[0,1] ϱ`: one common
point in time for all traces, which `F[0,1] ϱ` of STL does not ask. The `⇔` needs a state at every
time, to put a trace through each state of `R(t)`.

## Inputs
* `R` – reach sequence
* `ϱ` – predicate

## Hypotheses
* `hne` – all reach sets are nonempty

## Conclusion
* the RTL eventually matches eventually at some time of the traces

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

theorem RTL.finally_A_iff {R : ℝ≥0 → Set X} (hne : ∀ t, (R t).Nonempty)
    (ϱ : Pform X) : -- --- CONCL ---
    ((RTL.Formula.finally 0 1 (.A ϱ)).Sat R ↔
        ∃ t, t ≤ 1 ∧ (STL.Formula.finally t t (STL.Formula.ofPform ϱ)).HoldsOn
          (ReachSequence.traceSet R)) ∧
      ((∃ t, t ≤ 1 ∧ (STL.Formula.finally t t (STL.Formula.ofPform ϱ)).HoldsOn
          (ReachSequence.traceSet R)) →
        (STL.Formula.finally 0 1 (STL.Formula.ofPform ϱ)).HoldsOn
          (ReachSequence.traceSet R)) := by -- --- PROOF ---
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- the common time `t` and its all-states predicate
    rintro ⟨t, -, ht, hA, -⟩
    refine ⟨t, ht, fun ξ hξ => ⟨t, le_rfl, le_rfl, ?_, fun _ _ => trivial⟩⟩
    exact (STL.Formula.sat_ofPform ϱ _).2 (hA _ (by simpa [Time.shift] using hξ t))
  · rintro ⟨t, ht, h⟩
    refine ⟨t, zero_le, ht, ?_, fun _ _ _ _ => trivial⟩
    -- the predicate holds of the trace through any state of `R(t)`, so of all of them
    intro r hr
    have := (ReachSequence.forall_traceSet_sat_iff hne t ϱ).1 (fun ξ hξ => by
      obtain ⟨s, hs₁, hs₂, hs, -⟩ := h ξ hξ
      obtain rfl : s = t := le_antisymm hs₂ hs₁
      simpa [Time.shift, STL.Formula.sat_ofPform] using hs)
    simpa [Time.shift] using this r (by simpa [Time.shift] using hr)
  · -- a common time is a time in `[0,1]` for each trace
    rintro ⟨t, ht, h⟩ ξ hξ
    obtain ⟨s, hs₁, hs₂, hs, -⟩ := h ξ hξ
    exact ⟨s, zero_le, hs₂.trans ht, hs, fun _ _ => trivial⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

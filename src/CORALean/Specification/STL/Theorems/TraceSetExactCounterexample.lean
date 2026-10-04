import CORALean.Specification.STL.Definitions.ReachSequence

/-!
# An exact reach sequence can have more traces than the system

[1, Fig. 3]: `C(R)` "contains the set of traces `Traces(S)` and potentially additional
traces (even if `R` is exact)". Two constant traces, `false` and `true`, have the exact reach
sequence `R(t) = Bool`, which also holds every trace that switches.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSequence.exists_exact_traceSet_ne :
    ∃ (Traces : Set (ℝ≥0 → Bool)) (R : ℝ≥0 → Set Bool),
      ReachSequence.IsExact R Traces ∧ ReachSequence.traceSet R ≠ Traces := by -- --- PROOF ---
  -- the two constant traces, and the full set of values at each time
  refine ⟨{fun _ => false, fun _ => true}, fun _ => Set.univ, ?_, ?_⟩
  · intro t
    ext b
    simp only [Set.mem_univ, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
    cases b
    · exact ⟨fun _ => false, Or.inl rfl, rfl⟩
    · exact ⟨fun _ => true, Or.inr rfl, rfl⟩
  · intro h
    -- a trace that switches at time `1` is in `C(R)` but not a constant one
    have hmem : (fun t : ℝ≥0 => decide (t < 1)) ∈
        ReachSequence.traceSet (fun _ => (Set.univ : Set Bool)) :=
      fun _ => Set.mem_univ _
    rw [h] at hmem
    rcases hmem with h0 | h1
    · have := congrFun h0 0
      simp at this
    · have := congrFun h1 1
      simp at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

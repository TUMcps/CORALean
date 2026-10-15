module

public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalAt

@[expose] public section

/-!
# A three-valued signal is the join of its refinements

For a valid three-valued signal `Λ`, `Λ(t) = ⌊Λ⌋(t) ⊔₁ ⌈Λ⌉(t)` at every time `t ≥ 0`
([1, Sec. 4.2 (refinements)]).

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.at_eq_join (s : KleeneSignal ℝ) (hs : s.IsValid) (t : ℝ) (ht : 0 ≤ t) :
    s.at t = Kleene.join ((s.toBoolSignal false).at t) ((s.toBoolSignal true).at t) := by
  rw [(KleeneSignal.toBoolSignal_at s hs t ht).1, (KleeneSignal.toBoolSignal_at s hs t ht).2]
  exact (Kleene.join_floor_ceil _).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

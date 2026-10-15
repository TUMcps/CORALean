module

public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalAt

@[expose] public section

/-!
# A four-valued signal is the join of its refinements

For a valid four-valued signal `Λ̃`, `Λ̃(t) = ⌊Λ̃⌋(t) ⊔₂ ⌈Λ̃⌉(t)` at every time `t ≥ 0`
([1, Sec. 4.3 (refinements)]).

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

theorem FourValuedSignal.at_eq_join (s : FourValuedSignal ℝ) (hs : s.IsValid) (t : ℝ)
    (ht : 0 ≤ t) :
    s.at t = FourValued.join ((s.toKleeneSignal Kleene.ff).at t)
      ((s.toKleeneSignal Kleene.tt).at t) := by
  rw [(s.toKleeneSignal_at hs t ht).1, (s.toKleeneSignal_at hs t ht).2]
  exact (FourValued.join_floor_ceil _).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

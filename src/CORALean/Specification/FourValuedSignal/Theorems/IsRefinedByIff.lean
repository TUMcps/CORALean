module

public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalAt

@[expose] public section

/-!
# A Kleene signal refines a four-valued one between `⌊Λ̃⌋` and `⌈Λ̃⌉`

For a valid four-valued signal `Λ̃` and a Kleene signal `Λ`, `Λ ≺ Λ̃` iff `⌊Λ̃⌋ ⊑ₜ Λ ⊑ₜ ⌈Λ̃⌉` at
every time `t ≥ 0`, with `⌊Λ̃⌋ = toKleeneSignal(Λ̃,False)` and `⌈Λ̃⌉ = toKleeneSignal(Λ̃,True)`
([1, Sec. 4.3 (refinements)]); and `Λ̃` is recovered as `⌊Λ̃⌋ ⊔₂ ⌈Λ̃⌉`.

## Inputs
* `s` – four-valued signal
* `k` – three-valued signal

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* refinement holds iff the signal lies between the two refinements

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.isRefinedBy_iff (s : FourValuedSignal ℝ) (hs : s.IsValid)
    (k : KleeneSignal ℝ) :
    s.IsRefinedBy k ↔ ∀ t : ℝ, 0 ≤ t → (s.toKleeneSignal Kleene.ff).at t ≤ k.at t ∧
      k.at t ≤ (s.toKleeneSignal Kleene.tt).at t := by
  refine forall_congr' fun t => forall_congr' fun ht => ?_
  rw [(s.toKleeneSignal_at hs t ht).1, (s.toKleeneSignal_at hs t ht).2]
  exact FourValued.isRefinedBy_iff _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

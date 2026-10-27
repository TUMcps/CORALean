module

public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalAt

@[expose] public section

/-!
# A Boolean signal refines a three-valued one between `⌊Λ⌋` and `⌈Λ⌉`

For a valid three-valued signal `Λ` and a Boolean signal `λ`, `λ ≺ Λ` iff `⌊Λ⌋ ⊑ₜ λ ⊑ₜ ⌈Λ⌉` at
every time `t ≥ 0`, with `⌊Λ⌋ = toBoolSignal(Λ,false)` and `⌈Λ⌉ = toBoolSignal(Λ,true)`
([1, Sec. 4.2 (refinements)]); and `Λ` is recovered as `⌊Λ⌋ ⊔₁ ⌈Λ⌉`.

## Inputs
* `s` – three-valued signal
* `l` – Boolean signal

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* refinement holds iff the Boolean signal lies between the two refinements

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.isRefinedBy_iff (s : KleeneSignal ℝ) (hs : s.IsValid)
    (l : PointSegmentSignal ℝ) :
    s.IsRefinedBy l ↔ ∀ t : ℝ, 0 ≤ t → (s.toBoolSignal false).at t ≤ l.at t ∧
      l.at t ≤ (s.toBoolSignal true).at t := by
  refine forall_congr' fun t => forall_congr' fun ht => ?_
  rw [(KleeneSignal.toBoolSignal_at s hs t ht).1, (KleeneSignal.toBoolSignal_at s hs t ht).2]
  exact Kleene.isRefinedBy_iff _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

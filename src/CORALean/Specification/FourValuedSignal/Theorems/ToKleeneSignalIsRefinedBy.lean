module

public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalAt

@[expose] public section

/-!
# The refinements `toKleeneSignal` returns are refinements

For a valid four-valued signal `Λ̃`, `toKleeneSignal(Λ̃,mapInconclusiveTo)` refines `Λ̃` in the
sense of [1, Sec. 4.3 (refinements)], `Λ ≺ Λ̃`, for either value of `mapInconclusiveTo`: `⌊Λ̃⌋` and
`⌈Λ̃⌉` are refinements of `Λ̃`.

## Inputs
* `s` – four-valued signal
* `v` – value for inconclusive times

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* the signal is refined by its three-valued conversion

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

theorem FourValuedSignal.toKleeneSignal_isRefinedBy (s : FourValuedSignal ℝ) (hs : s.IsValid)
    (v : Kleene) : -- --- CONCL ---
    s.IsRefinedBy (s.toKleeneSignal v) := by -- --- PROOF ---
  intro t ht
  obtain ⟨h1, h2⟩ := (s.toKleeneSignal_spec hs v).2 t ht
  intro hne
  rw [h2 hne]
  generalize s.at t = k at hne ⊢
  cases k <;> first | exact absurd rfl hne | rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

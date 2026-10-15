module

public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalAt

@[expose] public section

/-!
# The refinements `toBoolSignal` returns are refinements

For a valid three-valued signal `Λ`, `toBoolSignal(Λ,mapUnknownTo)` refines `Λ` in the sense of
[1, Sec. 4.2 (refinements)], `λ ≺ Λ`, for either value of `mapUnknownTo`: `⌊Λ⌋` and `⌈Λ⌉` are
refinements of `Λ`.

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

theorem KleeneSignal.toBoolSignal_isRefinedBy (s : KleeneSignal ℝ) (hs : s.IsValid) (v : Bool) :
    s.IsRefinedBy (s.toBoolSignal v) := by -- --- PROOF ---
  intro t ht
  obtain ⟨h1, h2⟩ := (KleeneSignal.toBoolSignal_spec s hs v).2 t ht
  intro hne
  rw [h2 hne]
  generalize s.at t = k at hne ⊢
  cases k <;> first | exact absurd rfl hne | rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

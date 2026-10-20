module

public import CORALean.Specification.Kleene.Operations.Basic
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalSpec

@[expose] public section

/-!
# The Boolean refinements of a three-valued signal are `⌊Λ⌋` and `⌈Λ⌉`

For a valid three-valued signal, `toBoolSignal(Λ,false)` is, at every time `t ≥ 0`, the Boolean
value `⌊Λ(t)⌋` with unknown replaced by `false`, and `toBoolSignal(Λ,true)` the value `⌈Λ(t)⌉`
with unknown replaced by `true`: the under- and the overapproximation of
[1, Sec. 4.2 (refinements)].

## Inputs
* `s` – three-valued signal
* `t` – time

## Hypotheses
* `hs` – the signal is valid
* `ht` – the time is nonnegative

## Conclusion
* the two refinements are the floor and ceiling of the value

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

theorem KleeneSignal.toBoolSignal_at (s : KleeneSignal ℝ) (hs : s.IsValid) (t : ℝ)
    (ht : 0 ≤ t) : -- --- CONCL ---
    (s.toBoolSignal false).at t = (s.at t).floor ∧
      (s.toBoolSignal true).at t = (s.at t).ceil := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := (KleeneSignal.toBoolSignal_spec s hs false).2 t ht
  obtain ⟨g1, g2⟩ := (KleeneSignal.toBoolSignal_spec s hs true).2 t ht
  by_cases hu : s.at t = Kleene.uu
  · rw [g1 hu, h1 hu, hu]
    exact ⟨rfl, rfl⟩
  · rw [g2 hu, h2 hu]
    generalize s.at t = k at hu ⊢
    cases k <;> first | exact absurd rfl hu | exact ⟨rfl, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

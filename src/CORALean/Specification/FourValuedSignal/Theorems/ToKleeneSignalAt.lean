module

public import CORALean.Specification.FourValued.Operations.Basic
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalSpec

@[expose] public section

/-!
# The Kleene refinements of a four-valued signal are `⌊Λ̃⌋` and `⌈Λ̃⌉`

For a valid four-valued signal, `toKleeneSignal(Λ̃,False)` is, at every time `t ≥ 0`, the Kleene
value `⌊Λ̃(t)⌋` with inconclusive replaced by `False`, and `toKleeneSignal(Λ̃,True)` the value
`⌈Λ̃(t)⌉` with inconclusive replaced by `True`: the under- and the overapproximation of
[1, Sec. 4.3 (refinements)].

## Inputs
* `s` – four-valued signal
* `t` – time

## Hypotheses
* `hs` – the signal is valid
* `ht` – the time is nonnegative

## Conclusion
* the two refinements are the floor and ceiling of the value

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

theorem FourValuedSignal.toKleeneSignal_at (s : FourValuedSignal ℝ) (hs : s.IsValid) (t : ℝ)
    (ht : 0 ≤ t) : -- --- CONCL ---
    (s.toKleeneSignal Kleene.ff).at t = (s.at t).floor ∧
      (s.toKleeneSignal Kleene.tt).at t = (s.at t).ceil := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := (s.toKleeneSignal_spec hs Kleene.ff).2 t ht
  obtain ⟨g1, g2⟩ := (s.toKleeneSignal_spec hs Kleene.tt).2 t ht
  by_cases hu : s.at t = FourValued.ii
  · rw [g1 hu, h1 hu, hu]
    exact ⟨rfl, rfl⟩
  · rw [g2 hu, h2 hu]
    generalize s.at t = k at hu ⊢
    cases k <;> first | exact absurd rfl hu | exact ⟨rfl, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

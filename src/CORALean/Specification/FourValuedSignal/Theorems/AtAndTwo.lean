module

public import CORALean.Specification.FourValuedSignal.Theorems.AtAnd
public import CORALean.Specification.FourValued.Theorems.Basic

@[expose] public section

/-!
# The conjunction of two four-valued signals, at a time

For two valid signals the conjunction `fourValuedSignal.and_` exists, is valid and is, at each time
`t ≥ 0`, `fourValued.and` of the two values there: the pointwise form of `FourValuedSignal.at_and`
for a binary conjunction, which is how the syntax tree and the semantics combine two operands.

## Inputs
* `sigs` – the two four-valued signals

## Hypotheses
* `hv` – the signals are valid

## Conclusion
* the conjunction is valid and is `&` of the two values at every time `t ≥ 0`
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.at_and_two (sigs : Fin 2 → FourValuedSignal ℝ)
    (hv : ∀ k, (sigs k).IsValid) : -- --- CONCL ---
    ∃ r, FourValuedSignal.and_ sigs = some r ∧ r.IsValid ∧
      ∀ t : ℝ, 0 ≤ t → r.at t = ((sigs 0).at t).and ((sigs 1).at t) := by -- --- PROOF ---
  obtain ⟨r, hr, hv', h⟩ := FourValuedSignal.at_and sigs hv
  refine ⟨r, hr, hv', fun t ht => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h t ht
  rw [Fin.forall_fin_two] at h1
  rw [Fin.exists_fin_two] at h2
  rw [Fin.forall_fin_two, Fin.exists_fin_two] at h3
  -- the value is fixed by when it is `True`, `False` and `Inconclusive`
  apply FourValued.eq_of_iff
  · rw [h1]; generalize (sigs 0).at t = a; generalize (sigs 1).at t = b
    cases a <;> cases b <;> simp [FourValued.and]
  · rw [h2]; generalize (sigs 0).at t = a; generalize (sigs 1).at t = b
    cases a <;> cases b <;> simp [FourValued.and]
  · rw [h3]; generalize (sigs 0).at t = a; generalize (sigs 1).at t = b
    cases a <;> cases b <;> simp [FourValued.and]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

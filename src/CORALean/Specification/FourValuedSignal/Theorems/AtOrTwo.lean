module

public import CORALean.Specification.FourValuedSignal.Theorems.AtOr
public import CORALean.Specification.FourValued.Theorems.Basic

@[expose] public section

/-!
# The disjunction of two four-valued signals, at a time

For two valid signals the disjunction `fourValuedSignal.or_` exists, is valid and is, at each time
`t ≥ 0`, `fourValued.or` of the two values there: the pointwise form of `FourValuedSignal.at_or`
for a binary disjunction.

## Inputs
* `sigs` – the two four-valued signals

## Hypotheses
* `hv` – the signals are valid

## Conclusion
* the disjunction is valid and is `|` of the two values at every time `t ≥ 0`
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.at_or_two (sigs : Fin 2 → FourValuedSignal ℝ)
    (hv : ∀ k, (sigs k).IsValid) : -- --- CONCL ---
    ∃ r, FourValuedSignal.or_ sigs = some r ∧ r.IsValid ∧
      ∀ t : ℝ, 0 ≤ t → r.at t = ((sigs 0).at t).or ((sigs 1).at t) := by -- --- PROOF ---
  obtain ⟨r, hr, hv', h⟩ := FourValuedSignal.at_or sigs hv
  refine ⟨r, hr, hv', fun t ht => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h t ht
  rw [Fin.exists_fin_two] at h1
  rw [Fin.forall_fin_two] at h2
  rw [Fin.forall_fin_two, Fin.exists_fin_two] at h3
  -- the value is fixed by when it is `True`, `False` and `Inconclusive`
  apply FourValued.eq_of_iff
  · rw [h1]; generalize (sigs 0).at t = a; generalize (sigs 1).at t = b
    cases a <;> cases b <;> simp [FourValued.or]
  · rw [h2]; generalize (sigs 0).at t = a; generalize (sigs 1).at t = b
    cases a <;> cases b <;> simp [FourValued.or]
  · rw [h3]; generalize (sigs 0).at t = a; generalize (sigs 1).at t = b
    cases a <;> cases b <;> simp [FourValued.or]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

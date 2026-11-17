module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyTimeSetdiff
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `LinearSys.verifyTimeSetdiff` removes only the closed step

A time `t` of an interval of `U` that lies in no interval of the result lies in `[t₀, t₁]`: an
interval disjoint from `(t₀, t₁)` is kept; of one that meets it, `[a, t₀]` keeps the times before
`t₀` and `[t₁, b]` those after `t₁`. Nothing is dropped, however short.

## Inputs
* `U` – unverified time intervals
* `t₀` – start of the verified step
* `t₁` – end of the verified step
* `t` – time
* `iv` – interval of `U`

## Hypotheses
* `hiv` – `iv` is an interval of `U`
* `ht` – `t` lies in `iv`
* `hnot` – `t` lies in no interval of the result

## Conclusion
* `t₀ ≤ t ≤ t₁`
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.mem_Icc_of_not_mem_verifyTimeSetdiff {U : List (ℚ × ℚ)} {t₀ t₁ : ℚ} {t : ℝ}
    {iv : ℚ × ℚ} (hiv : iv ∈ U) (ht : (iv.1 : ℝ) ≤ t ∧ t ≤ iv.2)
    (hnot : ∀ iv' ∈ LinearSys.verifyTimeSetdiff U t₀ t₁,
      ¬((iv'.1 : ℝ) ≤ t ∧ t ≤ iv'.2)) : -- --- CONCL ---
    (t₀ : ℝ) ≤ t ∧ t ≤ t₁ := by -- --- PROOF ---
  have hmem : ∀ iv', iv' ∈ (if t₁ ≤ iv.1 ∨ iv.2 ≤ t₀ then [iv] else
      (if iv.1 < t₀ then [(iv.1, t₀)] else []) ++ (if t₁ < iv.2 then [(t₁, iv.2)] else [])) →
      ¬((iv'.1 : ℝ) ≤ t ∧ t ≤ iv'.2) := fun iv' h =>
    hnot iv' (List.mem_flatMap.mpr ⟨iv, hiv, h⟩)
  by_cases hd : t₁ ≤ iv.1 ∨ iv.2 ≤ t₀
  · exact absurd ht (hmem iv (by simp [hd]))
  constructor
  · by_contra h
    replace h := not_le.mp h
    have h1 : iv.1 < t₀ := by exact_mod_cast lt_of_le_of_lt ht.1 h
    exact hmem (iv.1, t₀) (by simp [if_neg hd, h1]) ⟨ht.1, h.le⟩
  · by_contra h
    replace h := not_le.mp h
    have h2 : t₁ < iv.2 := by exact_mod_cast lt_of_lt_of_le h ht.2
    exact hmem (t₁, iv.2) (by simp [if_neg hd, h2]) ⟨h.le, ht.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

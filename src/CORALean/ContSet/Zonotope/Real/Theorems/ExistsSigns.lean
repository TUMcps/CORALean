module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Moving a point of a zonotope along its generators

[1, Lemma 3.2]: for every `x` in a zonotope with generators `g₁, …, g_M` (and `−g₁, …, −g_M`)
there is a choice of signs `σᵢ ∈ {−1, 1}` such that `x + ∑ tᵢ gᵢ` is in the zonotope whenever
each `tᵢ ∈ {0, σᵢ}`; in particular `x + g` or `x − g` is in it for every generator `g`. With
`x = c + ∑ yᵢ gᵢ`, take `σᵢ = 1` if `yᵢ ≤ 0` and `−1` otherwise: `yᵢ + tᵢ` stays in `[−1, 1]`.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 3.2]: signs `σ` with `x + ∑ tᵢ gᵢ ∈ Z` for `tᵢ ∈ {0, σᵢ}`; and `x ± gᵢ ∈ Z`. -/
theorem Zonotope.exists_signs (Z : Zonotope (Vec ℝ n)) {x : Vec ℝ n}
    (hx : x ∈ Z.construct) : -- --- CONCL ---
    (∃ σ : Fin Z.h → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ∀ t : Fin Z.h → ℝ, (∀ i, t i = 0 ∨ t i = σ i) →
        x + ∑ i, t i • Z.G i ∈ Z.construct)
    ∧ ∀ i, x + Z.G i ∈ Z.construct ∨ x - Z.G i ∈ Z.construct := by -- --- PROOF ---
  obtain ⟨y, hy, rfl⟩ := hx
  -- step toward the middle on each axis: up if the coefficient is negative, else down
  set σ : Fin Z.h → ℝ := fun i => if y i ≤ 0 then 1 else -1 with hσ
  have hstep : ∀ t : Fin Z.h → ℝ, (∀ i, t i = 0 ∨ t i = σ i) → ∀ i, |y i + t i| ≤ 1 := by
    intro t ht i
    have h := abs_le.1 (hy i)
    rcases ht i with h0 | h0
    · rw [h0, add_zero]; exact abs_le.2 h
    · rw [h0, hσ]
      by_cases hneg : y i ≤ 0
      · simp only [hneg, if_true]; rw [abs_le]; constructor <;> linarith
      · simp only [hneg, if_false]; rw [abs_le]; constructor <;> linarith [not_le.1 hneg]
  have hmem : ∀ t : Fin Z.h → ℝ, (∀ i, t i = 0 ∨ t i = σ i) →
      Z.c + ∑ i, y i • Z.G i + ∑ i, t i • Z.G i ∈ Z.construct := by
    intro t ht
    refine ⟨fun i => y i + t i, hstep t ht, ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
    abel
  refine ⟨⟨σ, fun i => ?_, fun t ht => hmem t ht⟩, fun i => ?_⟩
  · simp only [hσ]; split_ifs <;> simp
  · -- a single step along generator `i`
    have h1 := hmem (fun j => if j = i then σ i else 0) (fun j => by
      by_cases hj : j = i
      · simp [hj]
      · simp [hj])
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    by_cases hneg : y i ≤ 0
    · left
      simpa [hσ, hneg] using h1
    · right
      simpa [hσ, hneg, sub_eq_add_neg] using h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

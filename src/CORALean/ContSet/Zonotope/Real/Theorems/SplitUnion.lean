module

public import CORALean.ContSet.Zonotope.Real.Operations.Split
public import CORALean.ContSet.Zonotope.Real.Theorems.SumSmulUpdate
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# A split loses nothing

`split`'s two halves cover exactly the zonotope they came from
[1, Prop. 3.8]. Read on the coefficient cube: the `j`-th coefficient of a half
is an affine image of `[-1, 1]`, onto `[-1, 0]` for the first half and onto
`[0, 1]` for the second, and every other coefficient is carried across
unchanged. So it is one substitution each way, `β_j ↦ (β_j ∓ 1)/2` forwards and
`γ_j ↦ 2γ_j ± 1` back, the sign chosen by the sign of `γ_j`.

Nothing is over-approximated and nothing is assumed: the equality holds at every
zonotope and every generator index, including a zero generator, where both
halves are the original.

`(Z.split j).1.h` is `Z.h` only up to unfolding, and a `Finset.univ` carries its
`Fintype` instance along, so the two halves are restated by `rfl` first; after
that every sum here is `sum_smul_update` at different arguments.

It first appeared as [2, Prop. 3].

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
* [2] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The two halves of a split cover the zonotope they came from, exactly. -/
theorem Zonotope.split_union (Z : Zonotope α) (j : Fin Z.h) :
    (Z.split j).1.construct ∪ (Z.split j).2.construct = Z.construct := by -- --- PROOF ---
  have h₁ : (Z.split j).1.construct = {x | ∃ β : Fin Z.h → ℝ, (∀ k, |β k| ≤ 1) ∧
      x = Z.c - (2 : ℝ)⁻¹ • Z.G j
        + ∑ k, β k • Function.update Z.G j ((2 : ℝ)⁻¹ • Z.G j) k} := rfl
  have h₂ : (Z.split j).2.construct = {x | ∃ β : Fin Z.h → ℝ, (∀ k, |β k| ≤ 1) ∧
      x = Z.c + (2 : ℝ)⁻¹ • Z.G j
        + ∑ k, β k • Function.update Z.G j ((2 : ℝ)⁻¹ • Z.G j) k} := rfl
  rw [h₁, h₂]
  ext x
  simp only [Zonotope.construct, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨β, hβ, rfl⟩ | ⟨β, hβ, rfl⟩)
    -- the first half reads `β j` off `[-1, 1]` onto `[-1, 0]`
    · refine ⟨Function.update β j ((β j - 1) / 2), fun k => ?_, ?_⟩
      · rcases eq_or_ne k j with rfl | hk
        · rw [Function.update_self, abs_le]
          have hk := abs_le.mp (hβ k)
          constructor <;> linarith [hk.1, hk.2]
        · rw [Function.update_of_ne hk]; exact hβ k
      · have hL := Zonotope.sum_smul_update β Z.G j (β j) ((2 : ℝ)⁻¹ • Z.G j)
        rw [Function.update_eq_self] at hL
        have hR := Zonotope.sum_smul_update β Z.G j ((β j - 1) / 2) (Z.G j)
        rw [Function.update_eq_self] at hR
        rw [hL, hR, smul_smul]
        have hc : (β j - 1) / 2 = β j * 2⁻¹ - 2⁻¹ := by ring
        rw [hc, sub_smul]
        abel
    -- the second half onto `[0, 1]`, the centre moved the other way
    · refine ⟨Function.update β j ((β j + 1) / 2), fun k => ?_, ?_⟩
      · rcases eq_or_ne k j with rfl | hk
        · rw [Function.update_self, abs_le]
          have hk := abs_le.mp (hβ k)
          constructor <;> linarith [hk.1, hk.2]
        · rw [Function.update_of_ne hk]; exact hβ k
      · have hL := Zonotope.sum_smul_update β Z.G j (β j) ((2 : ℝ)⁻¹ • Z.G j)
        rw [Function.update_eq_self] at hL
        have hR := Zonotope.sum_smul_update β Z.G j ((β j + 1) / 2) (Z.G j)
        rw [Function.update_eq_self] at hR
        rw [hL, hR, smul_smul]
        have hc : (β j + 1) / 2 = β j * 2⁻¹ + 2⁻¹ := by ring
        rw [hc, add_smul]
        abel
  · rintro ⟨γ, hγ, rfl⟩
    have hL := Zonotope.sum_smul_update γ Z.G j (γ j) (Z.G j)
    simp only [Function.update_eq_self] at hL
    have hb := abs_le.mp (hγ j)
    rcases le_or_gt (γ j) 0 with hj | hj
    -- a nonpositive `γ j` comes from the first half, at `2 * γ j + 1`
    · refine Or.inl ⟨Function.update γ j (2 * γ j + 1), fun k => ?_, ?_⟩
      · rcases eq_or_ne k j with rfl | hk
        · rw [Function.update_self, abs_le]
          constructor <;> linarith [hb.1, hb.2]
        · rw [Function.update_of_ne hk]; exact hγ k
      · have hR := Zonotope.sum_smul_update γ Z.G j (2 * γ j + 1) ((2 : ℝ)⁻¹ • Z.G j)
        rw [hL, hR, smul_smul]
        have hc : (2 * γ j + 1) * 2⁻¹ = γ j + 2⁻¹ := by ring
        rw [hc, add_smul]
        abel
    -- a positive one from the second, at `2 * γ j - 1`
    · refine Or.inr ⟨Function.update γ j (2 * γ j - 1), fun k => ?_, ?_⟩
      · rcases eq_or_ne k j with rfl | hk
        · rw [Function.update_self, abs_le]
          constructor <;> linarith [hb.1, hb.2]
        · rw [Function.update_of_ne hk]; exact hγ k
      · have hR := Zonotope.sum_smul_update γ Z.G j (2 * γ j - 1) ((2 : ℝ)⁻¹ • Z.G j)
        rw [hL, hR, smul_smul]
        have hc : (2 * γ j - 1) * 2⁻¹ = γ j - 2⁻¹ := by ring
        rw [hc, sub_smul]
        abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

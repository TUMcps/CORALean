module

public import CORALean.ContSet.Zonotope.Real.Theorems.UnderSSubset
public import CORALean.ContSet.Zonotope.Real.Theorems.BoxSInterHyperplaneIff

@[expose] public section

/-!
# Under- and over-approximation meet a guard exactly when the zonotope does

[1, Thm. 1]: with `Ω̄ᵢ = Box_S(Ωᵢ)` and `Ω̲ᵢ` the under-approximation of [1, Sec. 5.1], if
the normal `n_e` of the guard `G_e = {x | n_e·x = f_e}` is in `S` then
`Ω̲ᵢ ∩ G_e ≠ ∅ ⟺ Ω̄ᵢ ∩ G_e ≠ ∅ ⟺ Ωᵢ ∩ G_e ≠ ∅`. Stated for any zonotope `Z` and `n_e = s_j`.
`Z̲ ⊆ Z ⊆ Box_S(Z)` (`Zonotope.underS_subset`) gives one direction; for the other,
`Box_S(Z)` meeting `G_e` puts `f_e` between `m_j` and `M_j` ([1, Prop. 3]), and the segment
`u + t g_j`, `t ∈ [-1, 1]`, inside `Z̲`, runs from `m_j` to `M_j` along `s_j`, since
`g_j·s_j = Σₖ |vₖ·s_j|`.

## Inputs
* `Z` – zonotope
* `s` – directions
* `j` – direction index
* `fₑ` – hyperplane offset

## Hypotheses
* none

## Conclusion
* the hyperplane meets the under-approximation iff it meets the box iff it meets `Z`

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of Linear
      Time-Invariant Systems with Inputs". Hybrid Systems: Computation and Control, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n ℓ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: for `n_e = s_j`, `Z̲ ∩ G_e ≠ ∅ ⟺ Box_S(Z) ∩ G_e ≠ ∅ ⟺ Z ∩ G_e ≠ ∅`. -/
theorem Zonotope.underS_inter_hyperplane_iff (Z : Zonotope (Vec ℝ n)) (s : Fin ℓ → Vec ℝ n)
    (j : Fin ℓ) (fₑ : ℝ) : -- --- CONCL ---
    ((∃ x ∈ Z.underS s, x ⬝ᵥ s j = fₑ) ↔ ∃ x ∈ Z.boxS (Finset.univ.image s), x ⬝ᵥ s j = fₑ) ∧
      ((∃ x ∈ Z.boxS (Finset.univ.image s), x ⬝ᵥ s j = fₑ) ↔
        ∃ x ∈ Z.construct, x ⬝ᵥ s j = fₑ) := by -- --- PROOF ---
  -- a sign times its argument is the modulus
  have hsm : ∀ r : ℝ, Real.sign r * r = |r| := fun r => by
    rcases lt_trichotomy r 0 with h | h | h
    · rw [Real.sign_of_neg h, neg_one_mul, abs_of_neg h]
    · rw [h, Real.sign_zero, zero_mul, abs_zero]
    · rw [Real.sign_of_pos h, one_mul, abs_of_pos h]
  -- `Z̲ ⊆ Z`
  have hsub := Z.underS_subset s
  -- along `s_j`, the offset `g_j` reaches `Σₖ |vₖ·s_j|`
  have hdot : Z.extremalGen (s j) ⬝ᵥ s j = ∑ k, |Z.G k ⬝ᵥ s j| := by
    simp only [Zonotope.extremalGen, sum_dotProduct, smul_dotProduct, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [dotProduct_comm (s j), hsm]
  have h3 := Z.boxS_inter_hyperplane_iff (Finset.mem_image_of_mem s (Finset.mem_univ j)) fₑ
  refine ⟨⟨fun ⟨x, hx, h⟩ => h3.2 ⟨x, hsub hx, h⟩, fun hb => ?_⟩, h3⟩
  -- `f_e` is within `σ` of `u·s_j`
  obtain ⟨hlo, hhi⟩ := (Z.inter_hyperplane_iff (s j) fₑ).1 (h3.1 hb)
  set σ := ∑ k, |Z.G k ⬝ᵥ s j| with hσ
  set t := (fₑ - Z.c ⬝ᵥ s j) / σ
  by_cases h0 : σ = 0
  · -- no generator moves `s_j·x`: the center is on the guard
    refine ⟨Z.c, ⟨0, by simp, by simp⟩, by linarith⟩
  · -- the point `u + t g_j` with `|t| ≤ 1`
    have hσpos : 0 < σ := lt_of_le_of_ne (Finset.sum_nonneg fun k _ => abs_nonneg _) (Ne.symm h0)
    have ht : |t| ≤ 1 := by
      rw [abs_div, abs_of_pos hσpos, div_le_one hσpos, abs_le]
      constructor <;> linarith
    refine ⟨Z.c + t • Z.extremalGen (s j),
      ⟨fun i => if i = j then t else 0, ?_, ?_⟩, ?_⟩
    · simpa [apply_ite, Finset.sum_ite_eq'] using ht
    · simp [ite_smul, Finset.sum_ite_eq']
    · rw [add_dotProduct, smul_dotProduct, hdot, smul_eq_mul]
      rw [div_mul_cancel₀ _ h0]
      ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

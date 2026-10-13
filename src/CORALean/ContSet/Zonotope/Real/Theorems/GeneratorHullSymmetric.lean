import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.Zonotope.Real.Theorems.GeneratorHullEq
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A zonotope with symmetric generators is the image of the cube [-1, 1]

[1, Lemma 3.1]: if the generators come as `g₁, …, g_M, −g₁, …, −g_M` ([1, Eq. 13]), the
evolution `{s} ⊕ g₁ ⊕ ⋯ ⊕ (−g_M)` is `{s + G α | α ∈ [−1, 1]^M}` for `G = (g₁, …, g_M)`: the
two coefficients of `gᵢ` and `−gᵢ`, both in `[0, 1]`, combine to `αᵢ − αᵢ'`, which ranges over
all of `[−1, 1]`. The paper's shift is `0` ([1, Eq. 10]); it holds at any `s`.

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

/-- [1, Lemma 3.1]: the evolution of `s` by `g, −g` is `Zonotope.construct ⟨M, s, g⟩`. -/
theorem Zonotope.generatorHull_symmetric (s : Vec ℝ n) (M : ℕ) (g : Fin M → Vec ℝ n) :
    Zonotope.generatorHull s (M + M) (Fin.append g (-g))
      = (Zonotope.mk M s g).construct := by -- --- PROOF ---
  rw [Zonotope.generatorHull_eq]
  ext y
  simp only [Set.mem_setOf_eq, Zonotope.construct]
  constructor
  · -- the coefficient of `gᵢ` is the difference of those of `gᵢ` and `−gᵢ`
    rintro ⟨α, hα, rfl⟩
    refine ⟨fun i => α (Fin.castAdd M i) - α (Fin.natAdd M i), fun i => ?_, ?_⟩
    · have h1 := hα (Fin.castAdd M i)
      have h2 := hα (Fin.natAdd M i)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, smul_neg, sub_smul,
        Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      abel
  · -- positive and negative parts of `βᵢ` are the two coefficients
    rintro ⟨β, hβ, rfl⟩
    refine ⟨Fin.append (fun i => max (β i) 0) (fun i => max (-β i) 0), fun i => ?_, ?_⟩
    · -- both parts lie in `[0, 1]`
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have := abs_le.1 (hβ j)
        simp only [Fin.append_left, Set.mem_Icc]
        exact ⟨le_max_right _ _, max_le this.2 zero_le_one⟩
      · have := abs_le.1 (hβ j)
        simp only [Fin.append_right, Set.mem_Icc]
        exact ⟨le_max_right _ _, max_le (by linarith [this.1]) zero_le_one⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, smul_neg,
        Finset.sum_neg_distrib]
      congr 1
      rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul]
      congr 1
      rcases le_total 0 (β i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Taylm.Real.Operations.Degree

@[expose] public section

/-!
# An exponent of degree one is a unit vector

A sum of naturals equal to one has exactly one summand one and the others zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.degree_eq_one {e : Fin n → ℕ} (h : Taylm.degree e = 1) :
    ∃ k, e = Pi.single k 1 := by -- --- PROOF ---
  unfold Taylm.degree at h
  obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, e k ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [Finset.sum_eq_zero hc] at h
    exact zero_ne_one h
  have hrest : ∑ j ∈ Finset.univ.erase k, e j = 1 - e k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h; omega
  have hk1 : e k = 1 := by
    have := Finset.sum_nonneg (s := Finset.univ.erase k) fun j _ => Nat.zero_le (e j)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h; omega
  refine ⟨k, funext fun j => ?_⟩
  by_cases hj : j = k
  · subst hj; simp [hk1]
  · rw [Pi.single_eq_of_ne hj]
    rw [hk1, Nat.sub_self] at hrest
    exact (Finset.sum_eq_zero_iff.1 hrest) j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

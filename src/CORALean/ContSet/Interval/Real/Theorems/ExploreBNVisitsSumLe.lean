module

public import CORALean.ContSet.Interval.Real.Theorems.ExploreBNStepSpec
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# `EXPLORE BN` visits only vertices below the plane

[1, Alg. 2] starts from `(*, …, *)`, whose vertex `0` is below `Σᵢ xᵢ = α` when `α ≥ 0`, and
every face it forms is a piece `(v₁, …, v_j, b_{j+1}, …, b_{i-1}, 0, *, …)` of the partition of
[1, Lemma 6.2], whose own vertex lies below the visited `w = (…, b_{j+1}, …, b_k, 0, …)`. So
every visited `w` has `Σᵢ wᵢ ≤ α`, and `FIND SOLUTIONS(w)` adds `α' = α - Σᵢ wᵢ ≥ 0` upwards.
By strong induction on the number of undefined labels, as the recursion runs.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
theorem Interval.exploreBNVisits_sum_le {b : Vec ℝ n} {α : ℝ}
    (hb0 : ∀ i, 0 ≤ b i) : -- --- CONCL ---
    ∀ (j : ℕ) (p : Fin n → Bool), j ≤ n →
      ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (fun i => if (i : ℕ) < j then p i else false) i
        ≤ α →
      ∀ w ∈ Interval.exploreBNVisits b α j p,
        ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner w i ≤ α := by -- --- PROOF ---
  intro j
  induction hm : n - j using Nat.strong_induction_on generalizing j with
  | _ m ih =>
  intro p hj hP w hw
  obtain ⟨hmono, hjk, hkn, hPk, -⟩ := Interval.exploreBN_step_spec b α j p hj hb0 hP
  rw [Interval.exploreBNVisits] at hw
  simp only at hw hmono hjk hkn hPk
  set k := max j (Nat.findGreatest (fun k => ∑ x, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
    (fun i : Fin n => if (i : ℕ) < j then p i else decide ((i : ℕ) < k)) x ≤ α) n) with hkdef
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hPk
  · split_ifs at hw with hk
    · obtain ⟨⟨i, hi⟩, -, hwi⟩ := List.mem_flatMap.mp hw
      have hi' := List.mem_range'_1.mp hi
      refine ih (n - (i + 1)) (by omega) (i + 1) rfl _ (by omega) ?_ w hwi
      -- the child's own vertex is `lab i`, below `lab k`
      have hchild : (fun m : Fin n => if (m : ℕ) < i + 1 then
          (if (m : ℕ) = i then false else if (m : ℕ) < j then p m else decide ((m : ℕ) < k))
          else false) = fun m : Fin n => if (m : ℕ) < j then p m else decide ((m : ℕ) < i) := by
        funext m
        by_cases h1 : (m : ℕ) < j
        · simp [h1, show (m : ℕ) < i + 1 by omega, show (m : ℕ) ≠ i by omega]
        · by_cases h2 : (m : ℕ) < i
          · simp [h1, h2, show (m : ℕ) < i + 1 by omega, show (m : ℕ) ≠ i by omega,
              show (m : ℕ) < k by omega]
          · by_cases h3 : (m : ℕ) = i
            · simp [h3, show ¬ i < j by omega]
            · simp [h1, h2, show ¬ (m : ℕ) < i + 1 by omega]
      rw [hchild]
      exact le_trans (hmono i k (by omega)) hPk
    · simp at hw

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

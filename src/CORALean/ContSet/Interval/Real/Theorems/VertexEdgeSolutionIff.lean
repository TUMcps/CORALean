module

public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A vertex and the solutions on the edges it raises

[1, Cor. 6.3 (1)], `j = n`: a vertex `v` of `[0, b₁] × … × [0, bₙ]` is a solution iff
`Σⱼ vⱼ = α`; otherwise at least one solution is at its edges iff `Σⱼ vⱼ < α` and some `vᵢ = 0`
has `bᵢ > α - Σⱼ vⱼ`, namely `(v₁, …, α - Σⱼ vⱼ, …, vₙ)`. True of the edges `v` raises, open at
the far end, the reading the low border vertices of [1, Def. 4] give; for every edge at `v`
the "only if" fails, `Interval.vertex_edge_solution_counterexample`.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Changing coordinate `i` of `v` from `0` to `a` adds `a` to the sum. -/
theorem aux_sum_update_zero' {v : Vec ℝ n} {i : Fin n} {a : ℝ} (hvi : v i = 0) :
    ∑ k, Function.update v i a k = ∑ k, v k + a := by -- --- PROOF ---
  have : ∀ k, Function.update v i a k = v k + if k = i then a else 0 := fun k => by
    by_cases hk : k = i
    · subst hk; simp [hvi]
    · simp [hk]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.vertex_edge_solution_iff {b : Vec ℝ n} (hb0 : ∀ i, 0 < b i) {α : ℝ}
    (l : Fin n → Bool) : -- --- STMT ---
    let v := (⟨0, b⟩ : Interval (Vec ℝ n)).corner l
    (v ∈ Interval.hyperplane 1 α ↔ ∑ i, v i = α) ∧
    ((∃ i, l i = false ∧ ∃ t, 0 < t ∧ t < b i ∧
        Function.update v i t ∈ Interval.hyperplane 1 α) ↔
      (∑ k, v k < α ∧ ∃ i, v i = 0 ∧ α - ∑ k, v k < b i)) ∧
    (∀ i, v i = 0 → ∑ k, v k < α → α - ∑ k, v k < b i →
      Function.update v i (α - ∑ k, v k) ∈
        (⟨0, b⟩ : Interval (Vec ℝ n)).construct ∩ Interval.hyperplane 1 α) := by -- --- PROOF ---
  intro v
  have hplane : ∀ x : Vec ℝ n, x ∈ Interval.hyperplane 1 α ↔ ∑ k, x k = α := fun x => by
    simp [Interval.hyperplane]
  -- with `bᵢ > 0`, a coordinate of the vertex is `0` exactly where its label is down
  have hv0 : ∀ i, v i = 0 ↔ l i = false := fun i => by
    simp only [v, Interval.corner]
    cases l i <;> simp [(hb0 i).ne']
  refine ⟨hplane v, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨i, hli, t, ht0, htb, hP⟩
    have hvi : v i = 0 := (hv0 i).mpr hli
    rw [hplane, aux_sum_update_zero' hvi] at hP
    exact ⟨by linarith, i, hvi, by linarith⟩
  -- conversely raise `vᵢ` to `α - Σⱼ vⱼ`
  · rintro ⟨hlt, i, hvi, hib⟩
    refine ⟨i, (hv0 i).mp hvi, α - ∑ k, v k, by linarith, hib, ?_⟩
    rw [hplane, aux_sum_update_zero' hvi]
    ring
  -- the named point: in the box, coordinate `i` at `α - Σⱼ vⱼ < bᵢ`, and on the plane
  · intro i hvi hlt hib
    refine ⟨fun k => ?_, ?_⟩
    · change 0 ≤ Function.update v i (α - ∑ k, v k) k ∧
        Function.update v i (α - ∑ k, v k) k ≤ b k
      by_cases hki : k = i
      · subst hki; simp only [Function.update_self]; constructor <;> linarith
      · rw [Function.update_of_ne hki]
        simp only [v, Interval.corner]
        cases l k <;> simp [(hb0 k).le]
    · rw [hplane, aux_sum_update_zero' hvi]
      ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

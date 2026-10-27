module

public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import CORALean.ContSet.Interval.Real.Theorems.CornerSumAddLe
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# An s-face meeting Eq. (5) has a unique vertex below the plane

[1, Lemma 6.1]: on an ordered box `[0, b₁] × … × [0, bₙ]`, an s-face `(v₁, …, v_j, *, …, *)`,
`j < n`, with `Σ_{i≤j} vᵢ ≤ α < b_{j+1} + Σ_{i≤j} vᵢ` (Eq. 5) has exactly one vertex `v` with
`Σᵢ vᵢ ≤ α`, its border vertex `(v₁, …, v_j, 0, …, 0)`: every other raises some `k > j`, and
`b_k ≥ b_{j+1}`. The paper's `b_{j+1}` is `b ⟨j, hj⟩` here, coordinates counted from `0`.

## Inputs
* `b` – upper bound vector
* `j` – index of the face
* `p` – prefix labels
* `α` – level of the plane

## Hypotheses
* `hb` – bounds nondecreasing
* `hb0` – bounds nonnegative
* `hj` – face index below the dimension
* `h5` – corner sum at the prefix at most the level, below the next bound

## Conclusion
* exactly one vertex of the face lies below the plane

## References

* [1] [C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection Problem".
      INFOCOMP Journal of Computer Science,
      2009.](../../../../../../references/2009/lara-infocomp-hyperbox-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.existsUnique_border_vertex {b : Vec ℝ n} (hb : Monotone b)
    (hb0 : ∀ i, 0 ≤ b i) {j : ℕ} (hj : j < n) (p : Fin n → Bool) {α : ℝ}
    (h5 : ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
        (fun i => if (i : ℕ) < j then p i else false) i ≤ α ∧
      α < b ⟨j, hj⟩ + ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
        (fun i => if (i : ℕ) < j then p i else false) i) : -- --- CONCL ---
    ∃! l, l ∈ Interval.prefixFace j p ∧
      ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner l i ≤ α := by -- --- PROOF ---
  refine ⟨fun i => if (i : ℕ) < j then p i else false, ⟨fun i hi => by simp [hi], h5.1⟩, ?_⟩
  rintro l ⟨hl, hlS⟩
  funext m
  by_cases hm : (m : ℕ) < j
  · simp [hm, hl m hm]
  -- a raised label `m ≥ j` would add `bₘ ≥ b_j` to the border vertex's sum
  simp only [hm, if_false]
  by_contra hlm
  rw [Bool.not_eq_false] at hlm
  have hle := Interval.corner_sum_add_le hb0 (m := m)
    (l := fun i => if (i : ℕ) < j then p i else false) (w := l)
    (fun i hi => by
      by_cases hij : (i : ℕ) < j
      · simp only [hij, if_true] at hi; rw [hl i hij]; exact hi
      · simp [hij] at hi)
    (by simp [hm]) hlm
  have hjm : b ⟨j, hj⟩ ≤ b m := hb (show (⟨j, hj⟩ : Fin n) ≤ m from by
    simp only [Fin.le_def]; omega)
  linarith [h5.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

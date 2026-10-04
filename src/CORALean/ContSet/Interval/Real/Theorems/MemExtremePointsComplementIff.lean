import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsInterHyperplaneIff

/-!
# The complement of a vertex of the cut is a vertex of the complementary cut

[1, Lemma 6.4]: for the box `[0, b₁] × … × [0, bₙ]`, a solution `c` of the intersection with
`Σᵢ xᵢ = α` has the complement `c' = b - c` as a solution of the intersection with
`Σᵢ xᵢ = Σᵢ bᵢ - α`. Stated for the vertices of the cut, the solutions the paper means, and as
an equivalence: `x ↦ b - x` maps the box onto itself and edges onto edges.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mem_extremePoints_complement_iff {b : Vec ℝ n} {α : ℝ} {c : Vec ℝ n} :
    c ∈ Set.extremePoints ℝ ((⟨0, b⟩ : Interval (Vec ℝ n)).construct ∩
        Interval.hyperplane 1 α) ↔
      b - c ∈ Set.extremePoints ℝ ((⟨0, b⟩ : Interval (Vec ℝ n)).construct ∩
        Interval.hyperplane 1 (∑ i, b i - α)) := by -- --- PROOF ---
  rw [Interval.mem_extremePoints_inter_hyperplane_iff (a := 1) (fun _ => by simp),
    Interval.mem_extremePoints_inter_hyperplane_iff (a := 1) (fun _ => by simp)]
  -- coordinatewise: `cᵢ ∈ [0, bᵢ]` iff `bᵢ - cᵢ ∈ [0, bᵢ]`, and the bounds swap
  have hbox : c ∈ (⟨0, b⟩ : Interval (Vec ℝ n)).construct ↔
      b - c ∈ (⟨0, b⟩ : Interval (Vec ℝ n)).construct := by
    constructor
    · intro h i
      have hi : 0 ≤ c i ∧ c i ≤ b i := h i
      show 0 ≤ b i - c i ∧ b i - c i ≤ b i
      constructor <;> linarith [hi.1, hi.2]
    · intro h i
      have hi : 0 ≤ b i - c i ∧ b i - c i ≤ b i := h i
      show 0 ≤ c i ∧ c i ≤ b i
      constructor <;> linarith [hi.1, hi.2]
  -- the sums add up to `Σᵢ bᵢ`
  have hplane : c ∈ Interval.hyperplane 1 α ↔ b - c ∈ Interval.hyperplane 1 (∑ i, b i - α) := by
    simp only [Interval.hyperplane, Set.mem_setOf_eq, Pi.one_apply, one_mul, Pi.sub_apply,
      Finset.sum_sub_distrib]
    constructor <;> intro h <;> linarith
  -- `0` and `bᵢ` trade places
  have hedge : (⟨0, b⟩ : Interval (Vec ℝ n)).OnEdge c ↔
      (⟨0, b⟩ : Interval (Vec ℝ n)).OnEdge (b - c) := by
    have hk : ∀ k, (c k = (0 : Vec ℝ n) k ∨ c k = b k) ↔
        ((b - c) k = (0 : Vec ℝ n) k ∨ (b - c) k = b k) := fun k => by
      simp only [Pi.zero_apply, Pi.sub_apply]
      constructor
      · rintro (h | h)
        · right; linarith
        · left; linarith
      · rintro (h | h)
        · right; linarith
        · left; linarith
    simp only [Interval.OnEdge, hk]
  rw [Set.mem_inter_iff, Set.mem_inter_iff, hbox, hplane, hedge]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

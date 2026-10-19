module

public import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsInterHyperplaneIff

@[expose] public section

/-!
# Translating a box to the origin

[1, Sec. 6.3 (translation)]: the box `[a₁, b₁] × … × [aₙ, bₙ]` cut by `Σᵢ xᵢ = α` maps to
`[0, b₁ - a₁] × … × [0, bₙ - aₙ]` cut by `Σᵢ x⋆ᵢ = α - Σᵢ aᵢ`, every solution `c⋆` of the latter
to the solution `c = c⋆ + a` of the former. The vertices of the two cuts correspond exactly.

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

theorem Interval.mem_extremePoints_translate_iff {I : Interval (Vec ℝ n)} {α : ℝ}
    {c : Vec ℝ n} : -- --- CONCL ---
    c ∈ Set.extremePoints ℝ (I.construct ∩ Interval.hyperplane 1 α) ↔
      c - I.inf ∈ Set.extremePoints ℝ ((⟨0, I.sup - I.inf⟩ : Interval (Vec ℝ n)).construct ∩
        Interval.hyperplane 1 (α - ∑ i, I.inf i)) := by -- --- PROOF ---
  rw [Interval.mem_extremePoints_inter_hyperplane_iff (a := 1) (fun _ => by simp),
    Interval.mem_extremePoints_inter_hyperplane_iff (a := 1) (fun _ => by simp)]
  -- coordinatewise: `cᵢ ∈ [aᵢ, bᵢ]` iff `cᵢ - aᵢ ∈ [0, bᵢ - aᵢ]`, the bounds kept
  have hbox : c ∈ I.construct ↔
      c - I.inf ∈ (⟨0, I.sup - I.inf⟩ : Interval (Vec ℝ n)).construct := by
    constructor
    · intro h i
      have hi : I.inf i ≤ c i ∧ c i ≤ I.sup i := h i
      show 0 ≤ c i - I.inf i ∧ c i - I.inf i ≤ I.sup i - I.inf i
      constructor <;> linarith [hi.1, hi.2]
    · intro h i
      have hi : 0 ≤ c i - I.inf i ∧ c i - I.inf i ≤ I.sup i - I.inf i := h i
      show I.inf i ≤ c i ∧ c i ≤ I.sup i
      constructor <;> linarith [hi.1, hi.2]
  -- the sum drops by `Σᵢ aᵢ`
  have hplane : c ∈ Interval.hyperplane 1 α ↔
      c - I.inf ∈ Interval.hyperplane 1 (α - ∑ i, I.inf i) := by
    simp only [Interval.hyperplane, Set.mem_setOf_eq, Pi.one_apply, one_mul, Pi.sub_apply,
      Finset.sum_sub_distrib]
    constructor <;> intro h <;> linarith
  -- a bound moves with the box
  have hedge : I.OnEdge c ↔ (⟨0, I.sup - I.inf⟩ : Interval (Vec ℝ n)).OnEdge (c - I.inf) := by
    have hk : ∀ k, (c k = I.inf k ∨ c k = I.sup k) ↔
        ((c - I.inf) k = (0 : Vec ℝ n) k ∨ (c - I.inf) k = (I.sup - I.inf) k) := fun k => by
      simp only [Pi.zero_apply, Pi.sub_apply]
      constructor
      · rintro (h | h)
        · left; linarith
        · right; linarith
      · rintro (h | h)
        · left; linarith
        · right; linarith
    simp only [Interval.OnEdge, hk]
  rw [Set.mem_inter_iff, Set.mem_inter_iff, hbox, hplane, hedge]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

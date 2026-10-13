import CORALean.ContSet.ConZonotope.Real.Operations.Plus

/-!
# `ConZonotope.plus` is exactly the Minkowski sum

The witness is `Fin.append β₁ β₂`, as for a zonotope [1, Prop. 1]. What the constraints add is
that the concatenated coefficients satisfy the combined polytope exactly when
each half satisfies its own — which is `HPolytope.mem_intersection_iff` composed with the
preimage being a preimage, and holds by `rfl` once `comap` is what pulls a block
back.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at `plus`'s generator count, stated through the projection
because that is the form the goal has and simp will not rewrite a binder's
type. -/
theorem ConZonotope.aux_sum_univ_plus {M : Type} [AddCommMonoid M] {cZ₁ cZ₂ : ConZonotope α}
    (f : Fin (cZ₁.h + cZ₂.h) → M) :
    ∑ j : Fin (cZ₁.plus cZ₂).h, f j
      = ∑ j, f (Fin.castAdd cZ₂.h j) + ∑ j, f (Fin.natAdd cZ₁.h j) :=
  Fin.sum_univ_add f

omit [Module ℝ α] in
/-- Each block answers to its own polytope. `β` is ascribed at the projection
spelling of the count: at `Vec ℝ (cZ₁.h + cZ₂.h)` the module instance `HPolytope`
needs is not found, the two spellings being distinct terms. -/
theorem ConZonotope.aux_mem_plus_P_iff (cZ₁ cZ₂ : ConZonotope α) (β : Vec ℝ (cZ₁.plus cZ₂).h) :
    β ∈ (cZ₁.plus cZ₂).P.construct ↔
      blockLeft cZ₁.h cZ₂.h β ∈ cZ₁.P.construct
        ∧ blockRight cZ₁.h cZ₂.h β ∈ cZ₂.P.construct :=
  HPolytope.mem_intersection_iff

theorem ConZonotope.aux_value_plus' (cZ₁ cZ₂ : ConZonotope α) (β : Fin (cZ₁.h + cZ₂.h) → ℝ) :
    (cZ₁.plus cZ₂).c + ∑ j : Fin (cZ₁.plus cZ₂).h, β j • (cZ₁.plus cZ₂).G j
      = (cZ₁.c + ∑ j, β (Fin.castAdd cZ₂.h j) • cZ₁.G j)
        + (cZ₂.c + ∑ j, β (Fin.natAdd cZ₁.h j) • cZ₂.G j) := by
  rw [ConZonotope.aux_sum_univ_plus]
  simp only [ConZonotope.plus, Fin.append_left, Fin.append_right]
  abel

theorem ConZonotope.aux_value_plus (cZ₁ cZ₂ : ConZonotope α)
    (β₁ : Fin cZ₁.h → ℝ) (β₂ : Fin cZ₂.h → ℝ) :
    (cZ₁.plus cZ₂).c + ∑ j : Fin (cZ₁.plus cZ₂).h, Fin.append β₁ β₂ j • (cZ₁.plus cZ₂).G j
      = (cZ₁.c + ∑ j, β₁ j • cZ₁.G j) + (cZ₂.c + ∑ j, β₂ j • cZ₂.G j) := by
  rw [ConZonotope.aux_value_plus']
  simp only [Fin.append_left, Fin.append_right]


-- =======================================  MAIN THEOREM  ======================================= --

-- both inclusions come off `aux_value_plus`, the polytope splitting with the blocks
theorem ConZonotope.plus_exact (cZ₁ cZ₂ : ConZonotope α) :
    cZ₁.construct + cZ₂.construct = (cZ₁.plus cZ₂).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_, ⟨β₁, hβ₁, hP₁, rfl⟩, _, ⟨β₂, hβ₂, hP₂, rfl⟩, rfl⟩
    refine ⟨Fin.append β₁ β₂, ?_, ?_, (ConZonotope.aux_value_plus cZ₁ cZ₂ β₁ β₂).symm⟩
    · refine Fin.addCases (fun l => ?_) fun l => ?_
      · rw [Fin.append_left]; exact hβ₁ l
      · rw [Fin.append_right]; exact hβ₂ l
    · refine (ConZonotope.aux_mem_plus_P_iff cZ₁ cZ₂ _).mpr ⟨?_, ?_⟩
      · rw [blockLeft_append]; exact hP₁
      · rw [blockRight_append]; exact hP₂
  · rintro _ ⟨β, hβ, hP, rfl⟩
    obtain ⟨hP₁, hP₂⟩ := (ConZonotope.aux_mem_plus_P_iff cZ₁ cZ₂ β).mp hP
    exact ⟨cZ₁.c + ∑ j, β (Fin.castAdd cZ₂.h j) • cZ₁.G j,
      ⟨fun j => β (Fin.castAdd cZ₂.h j), fun j => hβ _, hP₁, rfl⟩,
      cZ₂.c + ∑ j, β (Fin.natAdd cZ₁.h j) • cZ₂.G j,
      ⟨fun j => β (Fin.natAdd cZ₁.h j), fun j => hβ _, hP₂, rfl⟩,
      (ConZonotope.aux_value_plus' cZ₁ cZ₂ β).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

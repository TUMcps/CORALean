import CORALean.ContSet.ConZonotope.Real.Operations.Plus

/-!
# `ConZonotope.plus` is exactly the Minkowski sum

The witness is `Fin.append β₁ β₂`, as for a zonotope. What the constraints add is
that the concatenated coefficients satisfy the combined polytope exactly when
each half satisfies its own — which is `HPolytope.mem_and_iff` composed with the
preimage being a preimage, and holds by `rfl` once `comap` is what pulls a block
back.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at `plus`'s generator count, stated through the projection
because that is the form the goal has and simp will not rewrite a binder's
type. -/
theorem ConZonotope.aux_sum_univ_plus {M : Type} [AddCommMonoid M] {C₁ C₂ : ConZonotope α}
    (f : Fin (C₁.h + C₂.h) → M) :
    ∑ j : Fin (C₁.plus C₂).h, f j
      = ∑ j, f (Fin.castAdd C₂.h j) + ∑ j, f (Fin.natAdd C₁.h j) :=
  Fin.sum_univ_add f

omit [Module ℝ α] in
/-- Each block answers to its own polytope. `β` is ascribed at the projection
spelling of the count: at `Vec ℝ (C₁.h + C₂.h)` the module instance `HPolytope`
needs is not found, the two spellings being distinct terms. -/
theorem ConZonotope.aux_mem_plus_P_iff (C₁ C₂ : ConZonotope α) (β : Vec ℝ (C₁.plus C₂).h) :
    β ∈ (C₁.plus C₂).P.construct ↔
      blockLeft C₁.h C₂.h β ∈ C₁.P.construct
        ∧ blockRight C₁.h C₂.h β ∈ C₂.P.construct :=
  HPolytope.mem_and_iff

theorem ConZonotope.aux_value_plus' (C₁ C₂ : ConZonotope α) (β : Fin (C₁.h + C₂.h) → ℝ) :
    (C₁.plus C₂).c + ∑ j : Fin (C₁.plus C₂).h, β j • (C₁.plus C₂).G j
      = (C₁.c + ∑ j, β (Fin.castAdd C₂.h j) • C₁.G j)
        + (C₂.c + ∑ j, β (Fin.natAdd C₁.h j) • C₂.G j) := by
  rw [ConZonotope.aux_sum_univ_plus]
  simp only [ConZonotope.plus, Fin.append_left, Fin.append_right]
  abel

theorem ConZonotope.aux_value_plus (C₁ C₂ : ConZonotope α)
    (β₁ : Fin C₁.h → ℝ) (β₂ : Fin C₂.h → ℝ) :
    (C₁.plus C₂).c + ∑ j : Fin (C₁.plus C₂).h, Fin.append β₁ β₂ j • (C₁.plus C₂).G j
      = (C₁.c + ∑ j, β₁ j • C₁.G j) + (C₂.c + ∑ j, β₂ j • C₂.G j) := by
  rw [ConZonotope.aux_value_plus']
  simp only [Fin.append_left, Fin.append_right]


-- =======================================  MAIN THEOREM  ======================================= --

-- both inclusions come off `aux_value_plus`, the polytope splitting with the blocks
theorem ConZonotope.plus_exact (C₁ C₂ : ConZonotope α) :
    C₁.construct + C₂.construct = (C₁.plus C₂).construct := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_, ⟨β₁, hβ₁, hP₁, rfl⟩, _, ⟨β₂, hβ₂, hP₂, rfl⟩, rfl⟩
    refine ⟨Fin.append β₁ β₂, ?_, ?_, (ConZonotope.aux_value_plus C₁ C₂ β₁ β₂).symm⟩
    · refine Fin.addCases (fun l => ?_) fun l => ?_
      · rw [Fin.append_left]; exact hβ₁ l
      · rw [Fin.append_right]; exact hβ₂ l
    · refine (ConZonotope.aux_mem_plus_P_iff C₁ C₂ _).mpr ⟨?_, ?_⟩
      · rw [blockLeft_append]; exact hP₁
      · rw [blockRight_append]; exact hP₂
  · rintro _ ⟨β, hβ, hP, rfl⟩
    obtain ⟨hP₁, hP₂⟩ := (ConZonotope.aux_mem_plus_P_iff C₁ C₂ β).mp hP
    exact ⟨C₁.c + ∑ j, β (Fin.castAdd C₂.h j) • C₁.G j,
      ⟨fun j => β (Fin.castAdd C₂.h j), fun j => hβ _, hP₁, rfl⟩,
      C₂.c + ∑ j, β (Fin.natAdd C₁.h j) • C₂.G j,
      ⟨fun j => β (Fin.natAdd C₁.h j), fun j => hβ _, hP₂, rfl⟩,
      (ConZonotope.aux_value_plus' C₁ C₂ β).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ConZonotope.Real.Operations.CartProd
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Prod

@[expose] public section

/-!
# `ConZonotope.cartProd` is exactly the Cartesian product

The witness is `Fin.append β₁ β₂`, as for `plus_exact`: the concatenated coefficients satisfy
the combined polytope exactly when each half satisfies its own
(`HPolytope.mem_intersection_iff`), and the generator sum splits along `Prod.fst` and
`Prod.snd` because each generator sits at zero in the other coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] [Module ℝ β] in
/-- `Fin.sum_univ_add` at `cartProd`'s generator count, stated through the projection. -/
theorem ConZonotope.aux_sum_univ_cartProd {cZ₁ : ConZonotope α} {cZ₂ : ConZonotope β}
    (f : Fin (cZ₁.h + cZ₂.h) → α × β) :
    ∑ j : Fin (cZ₁.cartProd cZ₂).h, f j
      = ∑ j, f (Fin.castAdd cZ₂.h j) + ∑ j, f (Fin.natAdd cZ₁.h j) :=
  Fin.sum_univ_add f

omit [Module ℝ α] [Module ℝ β] in
/-- Each block answers to its own polytope, as `ConZonotope.aux_mem_plus_P_iff`. -/
theorem ConZonotope.aux_mem_cartProd_P_iff (cZ₁ : ConZonotope α) (cZ₂ : ConZonotope β)
    (β' : Vec ℝ (cZ₁.cartProd cZ₂).h) :
    β' ∈ (cZ₁.cartProd cZ₂).P.construct ↔
      blockLeft cZ₁.h cZ₂.h β' ∈ cZ₁.P.construct
        ∧ blockRight cZ₁.h cZ₂.h β' ∈ cZ₂.P.construct :=
  HPolytope.mem_intersection_iff

theorem ConZonotope.aux_value_cartProd (cZ₁ : ConZonotope α) (cZ₂ : ConZonotope β)
    (γ : Fin (cZ₁.h + cZ₂.h) → ℝ) : -- --- STMT ---
    (cZ₁.cartProd cZ₂).c + ∑ j : Fin (cZ₁.cartProd cZ₂).h, γ j • (cZ₁.cartProd cZ₂).G j
      = (cZ₁.c + ∑ j, γ (Fin.castAdd cZ₂.h j) • cZ₁.G j,
         cZ₂.c + ∑ j, γ (Fin.natAdd cZ₁.h j) • cZ₂.G j) := by -- --- PROOF ---
  rw [ConZonotope.aux_sum_univ_cartProd]
  simp only [ConZonotope.cartProd, Fin.append_left, Fin.append_right, Prod.smul_mk, smul_zero]
  refine Prod.ext ?_ ?_ <;> simp [Prod.fst_sum, Prod.snd_sum]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.cartProd_exact (cZ₁ : ConZonotope α) (cZ₂ : ConZonotope β) :
    cZ₁.construct ×ˢ cZ₂.construct = (cZ₁.cartProd cZ₂).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro ⟨_, _⟩ ⟨⟨β₁, hβ₁, hP₁, rfl⟩, ⟨β₂, hβ₂, hP₂, rfl⟩⟩
    refine ⟨Fin.append β₁ β₂, ?_, ?_, ?_⟩
    · refine Fin.addCases (fun l => ?_) fun l => ?_
      · rw [Fin.append_left]; exact hβ₁ l
      · rw [Fin.append_right]; exact hβ₂ l
    · refine (ConZonotope.aux_mem_cartProd_P_iff cZ₁ cZ₂ _).mpr ⟨?_, ?_⟩
      · rw [blockLeft_append]; exact hP₁
      · rw [blockRight_append]; exact hP₂
    · rw [ConZonotope.aux_value_cartProd]
      simp only [Fin.append_left, Fin.append_right]
  · rintro _ ⟨γ, hγ, hP, rfl⟩
    obtain ⟨hP₁, hP₂⟩ := (ConZonotope.aux_mem_cartProd_P_iff cZ₁ cZ₂ γ).mp hP
    rw [ConZonotope.aux_value_cartProd]
    exact ⟨⟨fun j => γ (Fin.castAdd cZ₂.h j), fun j => hγ _, hP₁, rfl⟩,
           ⟨fun j => γ (Fin.natAdd cZ₁.h j), fun j => hγ _, hP₂, rfl⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

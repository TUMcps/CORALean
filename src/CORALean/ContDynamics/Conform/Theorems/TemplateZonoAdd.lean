module

public import CORALean.ContDynamics.Conform.Definitions.TemplateZono
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The sum of two stretched templates

`⟨c₁, G₁ diag(α₁)⟩ ⊕ ⟨c₂, G₂ diag(α₂)⟩ = ⟨c₁ + c₂, [G₁ G₂] diag([α₁; α₂])⟩`, the generators
indexed by the sum of the two index types rather than renumbered.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

theorem Conform.templateZono_add {m : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (c₁ c₂ : Vec ℝ m) (G₁ : ι₁ → Vec ℝ m) (G₂ : ι₂ → Vec ℝ m) (α₁ : ι₁ → ℝ) (α₂ : ι₂ → ℝ) :
    Conform.templateZono c₁ G₁ α₁ + Conform.templateZono c₂ G₂ α₂
      = Conform.templateZono (c₁ + c₂) (Sum.elim G₁ G₂) (Sum.elim α₁ α₂) := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨_, ⟨β₁, hβ₁, rfl⟩, _, ⟨β₂, hβ₂, rfl⟩, rfl⟩
    refine ⟨Sum.elim β₁ β₂, fun j => ?_, ?_⟩
    · cases j with
      | inl j => exact hβ₁ j
      | inr j => exact hβ₂ j
    · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      abel
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨_, ⟨fun j => β (Sum.inl j), fun j => hβ _, rfl⟩,
      _, ⟨fun j => β (Sum.inr j), fun j => hβ _, rfl⟩, ?_⟩
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.Conform.Definitions.TemplateZono

@[expose] public section

/-!
# A translated stretched template

`d ⊕ ⟨c, G diag(α)⟩ = ⟨d + c, G diag(α)⟩`: translation moves the centre only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

theorem Conform.singleton_add_templateZono {m : ℕ} {ι : Type} [Fintype ι] (d c : Vec ℝ m)
    (G : ι → Vec ℝ m) (α : ι → ℝ) :
    {d} + Conform.templateZono c G α = Conform.templateZono (d + c) G α := by -- --- PROOF ---
  rw [Set.singleton_add]
  ext y
  constructor
  · rintro ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
    exact ⟨β, hβ, by dsimp only; abel⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨_, ⟨β, hβ, rfl⟩, by dsimp only; abel⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

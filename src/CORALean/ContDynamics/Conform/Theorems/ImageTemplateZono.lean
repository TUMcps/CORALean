import CORALean.ContDynamics.Conform.Definitions.TemplateZono
import Mathlib.Data.Matrix.Basic

/-!
# The linear image of a stretched template

`M ⟨c, G diag(α)⟩ = ⟨M c, M G diag(α)⟩`: the image keeps the stretch factors, so the
factors stay the unknowns after every linear map the reachable set applies.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Conform.image_templateZono {m m' : ℕ} {ι : Type} [Fintype ι] (M : Mat ℝ m' m)
    (c : Vec ℝ m) (G : ι → Vec ℝ m) (α : ι → ℝ) :
    (fun x => M *ᵥ x) '' Conform.templateZono c G α
      = Conform.templateZono (M *ᵥ c) (fun j => M *ᵥ G j) α := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
    exact ⟨β, hβ, by simp only [mulVec_add, mulVec_sum, mulVec_smul]⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨_, ⟨β, hβ, rfl⟩, by simp only [mulVec_add, mulVec_sum, mulVec_smul]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

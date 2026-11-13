module

public import CORALean.NN.Layers.Definitions.Tracks
public import CORALean.NN.Layers.Operations.Basic

@[expose] public section

/-!
# Tracking composes

The first layer's image keeps the generators of its argument in front, and the second layer's
image keeps those of the first image in front, which begin with the argument's. So the composite
keeps the generators of the argument in front of the second image, at the weights both extend.

## Inputs
* `L₂` – second layer
* `L₁` – first layer
* `f` – function of the first layer
* `g` – function of the second layer

## Hypotheses
* `h₂` – the second layer tracks its function
* `h₁` – the first layer tracks its function

## Conclusion
* the composite tracks the composite of the functions
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float
open scoped CORALean.Float

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n m k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.comp_tracks {L₂ : Layer 𝒵[𝕋] m k} {L₁ : Layer 𝒵[𝕋] n m} {f : Vec ℝ n → Vec ℝ m}
    {g : Vec ℝ m → Vec ℝ k} (h₂ : L₂.Tracks g) (h₁ : L₁.Tracks f) : -- --- CONCL ---
    (L₂.comp L₁).Tracks (g ∘ f) := by -- --- PROOF ---
  intro X
  obtain ⟨hle₁, H₁⟩ := h₁ X
  obtain ⟨hle₂, H₂⟩ := h₂ (L₁.enclose X)
  refine ⟨hle₁.trans hle₂, fun β x hx => ?_⟩
  -- the weights through the first image, then through the second
  obtain ⟨γ, hγ, hy⟩ := H₁ β x hx
  obtain ⟨δ, hδ, hz⟩ := H₂ γ (f x) hy
  exact ⟨δ, fun j => (hδ (Fin.castLE hle₁ j)).trans (hγ j), hz⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

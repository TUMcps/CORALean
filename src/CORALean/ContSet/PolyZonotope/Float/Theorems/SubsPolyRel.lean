module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.SubsRel
public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsPoly
public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsPoly

@[expose] public section

/-!
# `subsPoly` is the stored polynomial of an output

Each coefficient is the stored float, bracketed by itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.subsPoly_rel {nu : ℕ} (pZin : PolyZonotope (Vec 𝕋 nu)) (ii : Fin nu) :
    PolyZonotope.subsRel (pZin.subsPoly ii)
      (Real.PolyZonotope.subsPoly (InflatedContSet.nominal pZin) ii) := by -- --- PROOF ---
  refine List.Forall₂.cons ⟨rfl, le_refl _, le_refl _⟩ ?_
  generalize List.finRange pZin.h = L
  induction L with
  | nil => exact List.Forall₂.nil
  | cons j L ih => exact List.Forall₂.cons ⟨rfl, le_refl _, le_refl _⟩ ih

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

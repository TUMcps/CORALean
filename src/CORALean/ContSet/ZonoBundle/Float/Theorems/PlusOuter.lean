module

public import CORALean.ContSet.ZonoBundle.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

@[expose] public section

/-!
# `ZonoBundle.plus` over-approximates the Minkowski sum

Sound because `(⋂ᵢ Aᵢ) + (⋂ⱼ Bⱼ) ⊆ ⋂ᵢⱼ (Aᵢ + Bⱼ)`: a point from each
intersection sums into every pairwise sum, and `Zonotope.plus_outer` encloses
that pairwise sum — the exact layer reads it back through `plus_exact` instead,
which is the one step rounding takes away.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.plus_outer (zB₁ zB₂ : ZonoBundle (Vec 𝕋 n)) :
    zB₁.construct + zB₂.construct ⊆ (zB₁.plus zB₂).construct := by -- --- PROOF ---
  rintro _ ⟨a, ha, b, hb, rfl⟩
  simp only [ZonoBundle.construct, Set.mem_iInter] at ha hb ⊢
  intro p
  show a + b ∈ (Zonotope.plus (zB₁.Z _) (zB₂.Z _)).construct
  exact Zonotope.plus_outer _ _ (Set.add_mem_add (ha _) (hb _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

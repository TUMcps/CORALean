import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

/-!
# `ZonoBundle.plus` over-approximates the Minkowski sum

Sound because `(⋂ᵢ Aᵢ) + (⋂ⱼ Bⱼ) ⊆ ⋂ᵢⱼ (Aᵢ + Bⱼ)`: a point from each
intersection sums into every pairwise `Zonotope.plus`, `Zonotope.plus_exact`
reading that pairwise sum back as the two zonotopes it came from.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.plus_outer (B₁ B₂ : ZonoBundle α) :
    B₁.construct + B₂.construct ⊆ (B₁.plus B₂).construct := by -- --- PROOF ---
  rintro _ ⟨a, ha, b, hb, rfl⟩
  simp only [ZonoBundle.construct, Set.mem_iInter] at ha hb ⊢
  intro k
  show a + b ∈ (Zonotope.plus (B₁.Z _) (B₂.Z _)).construct
  rw [← Zonotope.plus_exact]
  exact Set.add_mem_add (ha _) (hb _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# `ZonoBundle.plus` over-approximates the Minkowski sum

Sound because `(⋂ᵢ Aᵢ) + (⋂ⱼ Bⱼ) ⊆ ⋂ᵢⱼ (Aᵢ + Bⱼ)` [1, Prop. 2]: a point from each
intersection sums into every pairwise `Zonotope.plus`, `Zonotope.plus_exact`
reading that pairwise sum back as the two zonotopes it came from.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

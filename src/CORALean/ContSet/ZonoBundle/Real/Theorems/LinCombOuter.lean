module

public import CORALean.ContSet.ZonoBundle.Real.Operations.LinComb
public import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter

@[expose] public section

/-!
# `ZonoBundle.linComb` over-approximates `Set.linComb`

Sound because a point `lam • a + (1 - lam) • b` with `a ∈ ⋂ᵢ Aᵢ` and
`b ∈ ⋂ⱼ Bⱼ` lies in `Set.linComb Aᵢ Bⱼ` for *every* pair `(i, j)` — the same
`lam` serving all of them — so it lies in the intersection of the pairwise
combinations, which `Zonotope.linComb_outer` reads each pair into.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.linComb_outer (B₁ B₂ : ZonoBundle α) :
    Set.linComb B₁.construct B₂.construct ⊆ (B₁.linComb B₂).construct := by -- --- PROOF ---
  rintro x ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩
  simp only [ZonoBundle.construct, Set.mem_iInter] at hy₁ hy₂ ⊢
  intro p
  show lam • y₁ + (1 - lam) • y₂ ∈ (Zonotope.linComb (B₁.Z _) (B₂.Z _)).construct
  exact Zonotope.linComb_outer _ _ ⟨y₁, hy₁ _, y₂, hy₂ _, lam, hlam, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

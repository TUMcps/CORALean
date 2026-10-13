import CORALean.ContSet.ZonoBundle.Float.Operations.LinComb
import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter

/-!
# `ZonoBundle.linComb` over-approximates `segments`

Sound because a point `lam • a + (1 - lam) • b` with `a ∈ ⋂ᵢ Aᵢ` and
`b ∈ ⋂ⱼ Bⱼ` lies in `segments Aᵢ Bⱼ` for *every* pair `(i, j)` — the same
`lam` serving all of them — so it lies in the intersection of the pairwise
combinations, which `Zonotope.linComb_outer` reads each pair into, rounding
and all.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.linComb_outer (zB₁ zB₂ : ZonoBundle (Vec 𝕋 n)) :
    segments zB₁.construct zB₂.construct ⊆ (zB₁.linComb zB₂).construct := by -- --- PROOF ---
  rintro x ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩
  simp only [ZonoBundle.construct, Set.mem_iInter] at hy₁ hy₂ ⊢
  intro p
  show lam • y₁ + (1 - lam) • y₂ ∈ (Zonotope.linComb (zB₁.Z _) (zB₂.Z _)).construct
  exact Zonotope.linComb_outer _ _ ⟨y₁, hy₁ _, y₂, hy₂ _, lam, hlam, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHull
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ConvHullSingleOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.LinCombOuter

@[expose] public section

/-!
# `ConPolyZono.convHull` contains the convex hull of the union

The union lies in the linear combination (`linComb_outer`, with a point of the other operand
to pair each with, which is what non-emptiness is for), and the combination's hull lies in
`convHullSingle` at `n + 1` copies (`convHullSingle_outer`). As over ℝ, both operands must be
non-empty and carry no independent generators; no condition on the exponent matrices enters.
Outer, never the exact hull.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.convHull_outer (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (hq₁ : cPZ₁.qI = 0) (hq₂ : cPZ₂.qI = 0)
    (hne₁ : cPZ₁.construct.Nonempty) (hne₂ : cPZ₂.construct.Nonempty) :
    convexHull ℝ (cPZ₁.construct ∪ cPZ₂.construct)
      ⊆ (cPZ₁.convHull cPZ₂).construct := by -- --- PROOF ---
  obtain ⟨y₁, hy₁⟩ := hne₁
  obtain ⟨y₂, hy₂⟩ := hne₂
  have hq : (cPZ₁.linComb cPZ₂).qI = 0 := by
    show cPZ₁.qI + cPZ₂.qI = 0
    omega
  -- the union sits inside the combination, and only here is a point needed
  have hsub : cPZ₁.construct ∪ cPZ₂.construct ⊆ (cPZ₁.linComb cPZ₂).construct := by
    refine subset_trans ?_ (ConPolyZono.linComb_outer cPZ₁ cPZ₂)
    rintro x (hx | hx)
    · exact ⟨x, hx, y₂, hy₂, 1, ⟨zero_le_one, le_refl 1⟩, by simp⟩
    · exact ⟨y₁, hy₁, x, hx, 0, ⟨le_refl 0, zero_le_one⟩, by simp⟩
  exact subset_trans (convexHull_mono hsub)
    (ConPolyZono.convHullSingle_outer (n + 1) _ hq le_rfl)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.HPolytope.Float.Theorems.ContractBoxOuter
public import CORALean.ContSet.VPolytope.Float.Operations.IntersectionCut
public import CORALean.ContSet.Interval.Float.Operations.IntersectionExact
public import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval

@[expose] public section

/-!
# The float `VPolytope.intersectionCut` contains the intersection

A point of both operands lies in both boxes, hence in their intersection, and in both
halfspace descriptions, which the cuts keep it through one after the other.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q₁ q₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.intersectionCut_outer (P₁ P₂ : VPolytope (Vec 𝕋 n)) (Aq₁ : Mat 𝕋 q₁ n)
    (Aq₂ : Mat 𝕋 q₂ n) :
    P₁.construct ∩ P₂.construct ⊆ (P₁.intersectionCut P₂ Aq₁ Aq₂).construct := by -- --- PROOF ---
  rintro x ⟨h₁, h₂⟩
  refine Interval.vPolytope_contains _ ?_
  refine (P₂.hPolytope Aq₂).contractBox_outer _ ⟨?_, P₂.hPolytope_contains Aq₂ h₂⟩
  refine (P₁.hPolytope Aq₁).contractBox_outer _ ⟨?_, P₁.hPolytope_contains Aq₁ h₁⟩
  rw [Interval.intersection_exact]
  exact ⟨P₁.interval_contains h₁, P₂.interval_contains h₂⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

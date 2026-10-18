module

public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusALeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusARight
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight

@[expose] public section

/-!
# Two constraint systems over disjoint factors, side by side

The rows of `plusA A₁ A₂` at the monomials of `plusE R₁ R₂` are each system's rows at its own
factors: the block-diagonal exponent matrix keeps either system's monomials blind to the other's
factors, and the block-diagonal matrix keeps its rows blind to the other's columns. What
`holds_plus_iff` reads row by row, as a vector identity any row condition can be read off.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two systems side by side over disjoint factors: the rows are each system's at its own. -/
theorem ConPolyZono.mulVec_plusA_plusE {p₁ p₂ m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat ℝ m₁ q₁)
    (A₂ : Mat ℝ m₂ q₂) (R₁ : Fin p₁ → Fin q₁ → ℕ) (R₂ : Fin p₂ → Fin q₂ → ℕ)
    (a : Fin (p₁ + p₂) → ℝ) : -- --- STMT ---
    ConPolyZono.plusA A₁ A₂ *ᵥ PolyZonotope.monomial (PolyZonotope.plusE R₁ R₂) a
      = Fin.append (A₁ *ᵥ PolyZonotope.monomial R₁ fun k => a (Fin.castAdd p₂ k))
          (A₂ *ᵥ PolyZonotope.monomial R₂ fun k => a (Fin.natAdd p₁ k)) := by -- --- PROOF ---
  refine funext (Fin.addCases (fun i => ?_) fun i => ?_)
  · have hm : (fun l => PolyZonotope.monomial (PolyZonotope.plusE R₁ R₂) a (Fin.castAdd q₂ l))
        = PolyZonotope.monomial R₁ (fun k => a (Fin.castAdd p₂ k)) :=
      funext fun l => PolyZonotope.monomial_plusE_left R₁ R₂ a l
    rw [ConPolyZono.mulVec_plusA_left, hm, Fin.append_left]
  -- the mirror on the right block, monomials again read off its own factors
  · have hm : (fun l => PolyZonotope.monomial (PolyZonotope.plusE R₁ R₂) a (Fin.natAdd q₁ l))
        = PolyZonotope.monomial R₂ (fun k => a (Fin.natAdd p₁ k)) :=
      funext fun l => PolyZonotope.monomial_plusE_right R₁ R₂ a l
    rw [ConPolyZono.mulVec_plusA_right, hm, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

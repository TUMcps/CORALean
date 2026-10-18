module

public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusALeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusARight
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight

@[expose] public section

/-!
# Two constraint systems over shared factors, stacked

The rows of `plusA A₁ A₂` at the monomials of `appendE R₁ R₂` are each system's rows at the same
factors: the exponent matrices sit side by side over one factor vector, and the block-diagonal
matrix keeps a row blind to the other system's columns. What `holds_shared_iff` reads row by row,
as a vector identity any row condition can be read off.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two systems stacked over shared factors: the rows are each system's at those factors. -/
theorem ConPolyZono.mulVec_plusA_appendE {p m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat ℝ m₁ q₁)
    (A₂ : Mat ℝ m₂ q₂) (R₁ : Fin p → Fin q₁ → ℕ) (R₂ : Fin p → Fin q₂ → ℕ)
    (a : Fin p → ℝ) : -- --- STMT ---
    ConPolyZono.plusA A₁ A₂ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE R₁ R₂) a
      = Fin.append (A₁ *ᵥ PolyZonotope.monomial R₁ a)
          (A₂ *ᵥ PolyZonotope.monomial R₂ a) := by -- --- PROOF ---
  refine funext (Fin.addCases (fun i => ?_) fun i => ?_)
  · have hm : (fun l => PolyZonotope.monomial (ConPolyZono.appendE R₁ R₂) a (Fin.castAdd q₂ l))
        = PolyZonotope.monomial R₁ a :=
      funext fun l => ConPolyZono.monomial_appendE_left R₁ R₂ a l
    rw [ConPolyZono.mulVec_plusA_left, hm, Fin.append_left]
  -- the mirror on the right block, its monomials read off the same factors
  · have hm : (fun l => PolyZonotope.monomial (ConPolyZono.appendE R₁ R₂) a (Fin.natAdd q₁ l))
        = PolyZonotope.monomial R₂ a :=
      funext fun l => ConPolyZono.monomial_appendE_right R₁ R₂ a l
    rw [ConPolyZono.mulVec_plusA_right, hm, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

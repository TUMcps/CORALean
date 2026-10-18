module

public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusALeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecPlusARight
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight

@[expose] public section

/-!
# Two constraint systems side by side hold exactly when each holds on its own factors

The block-diagonal exponent matrix is what makes the right-to-left direction
work, neither system's monomials seeing the other's.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two constraint systems side by side hold exactly when each holds on the
factors it came with; the block-diagonal exponent matrix is what makes the
right-to-left direction work, neither system's monomials seeing the other's. -/
theorem ConPolyZono.holds_plus_iff {p₁ p₂ m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat ℝ m₁ q₁)
    (b₁ : Interval (Vec ℝ m₁)) (R₁ : Fin p₁ → Fin q₁ → ℕ) (A₂ : Mat ℝ m₂ q₂)
    (b₂ : Interval (Vec ℝ m₂))
    (R₂ : Fin p₂ → Fin q₂ → ℕ) (a : Fin (p₁ + p₂) → ℝ) : -- --- STMT ---
    ConPolyZono.holds (ConPolyZono.plusA A₁ A₂) (ConPolyZono.plusB b₁ b₂)
        (PolyZonotope.plusE R₁ R₂) a
      ↔ ConPolyZono.holds A₁ b₁ R₁ (fun k => a (Fin.castAdd p₂ k))
        ∧ ConPolyZono.holds A₂ b₂ R₂ (fun k => a (Fin.natAdd p₁ k)) := by -- --- PROOF ---
  have hL : ∀ i : Fin m₁,
      (ConPolyZono.plusA A₁ A₂ *ᵥ PolyZonotope.monomial (PolyZonotope.plusE R₁ R₂) a)
          (Fin.castAdd m₂ i)
        = (A₁ *ᵥ PolyZonotope.monomial R₁ fun k => a (Fin.castAdd p₂ k)) i := by
    intro i
    have hm : (fun l => PolyZonotope.monomial (PolyZonotope.plusE R₁ R₂) a
          (Fin.castAdd q₂ l))
        = PolyZonotope.monomial R₁ (fun k => a (Fin.castAdd p₂ k)) :=
      funext fun l => PolyZonotope.monomial_plusE_left R₁ R₂ a l
    rw [ConPolyZono.mulVec_plusA_left, hm]
  -- the mirror on the right block, monomials again read off its own factors
  have hR : ∀ i : Fin m₂,
      (ConPolyZono.plusA A₁ A₂ *ᵥ PolyZonotope.monomial (PolyZonotope.plusE R₁ R₂) a)
          (Fin.natAdd m₁ i)
        = (A₂ *ᵥ PolyZonotope.monomial R₂ fun k => a (Fin.natAdd p₁ k)) i := by
    intro i
    have hm : (fun l => PolyZonotope.monomial (PolyZonotope.plusE R₁ R₂) a
          (Fin.natAdd q₁ l))
        = PolyZonotope.monomial R₂ (fun k => a (Fin.natAdd p₁ k)) :=
      funext fun l => PolyZonotope.monomial_plusE_right R₁ R₂ a l
    rw [ConPolyZono.mulVec_plusA_right, hm]
  -- both directions now, `plusB` splitting the bounds the same way the rows split
  constructor
  · intro hsat
    constructor
    · intro i
      have h := hsat (Fin.castAdd m₂ i)
      rw [hL i] at h
      simpa only [ConPolyZono.plusB, Fin.append_left] using h
    · intro i
      have h := hsat (Fin.natAdd m₁ i)
      rw [hR i] at h
      simpa only [ConPolyZono.plusB, Fin.append_right] using h
  · rintro ⟨h₁, h₂⟩
    refine Fin.addCases (fun i => ?_) fun i => ?_
    · rw [hL i]
      simpa only [ConPolyZono.plusB, Fin.append_left] using h₁ i
    · rw [hR i]
      simpa only [ConPolyZono.plusB, Fin.append_right] using h₂ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

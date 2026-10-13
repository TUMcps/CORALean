import CORALean.ContSet.Zonotope.Real.Operations.Bilin
import CORALean.Global.Cost

/-!
# `Zonotope.bilinCost`

Asserted, not proved: `Operations/Bilin.lean` applies the bilinear map `f` once
for the centre pair, once per generator of `Z₁` against the centre of `Z₂`,
once per generator of `Z₂` against the centre of `Z₁`, and once per pair of
generators: `1 + h₁ + h₂ + h₁ * h₂` applications. What one costs depends on `f`
and is a parameter. `Complexity/Space/` states the matching size, and the existing
`bilin_h_isBigO` there reads off the same product.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.bilin` costs when one application of `f` costs at most `cf`. -/
def Zonotope.bilinCost (cf : Cost) (h₁ h₂ : ℕ) : Cost := (1 + h₁ + h₂ + h₁ * h₂) • cf

/-- Monotone in both generator counts. -/
theorem Zonotope.bilinCost_mono {h₁ h₁' h₂ h₂' : ℕ} (cf : Cost) (h : h₁ ≤ h₁') (h' : h₂ ≤ h₂') :
    Zonotope.bilinCost cf h₁ h₂ ≤ Zonotope.bilinCost cf h₁' h₂' :=
  Nat.mul_le_mul_right _ (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left h _) h')
    (Nat.mul_le_mul h h'))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

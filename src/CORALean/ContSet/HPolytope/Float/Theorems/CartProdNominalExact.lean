module

public import CORALean.ContSet.HPolytope.Float.Operations.CartProd
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemPadRightNominalIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MemPadLeftNominalIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MemStackRowsNominalIff

@[expose] public section

/-!
# The nominal part of `HPolytope.cartProd` is the Cartesian product of the nominal parts

A point is in the stacked rows iff its left block meets the first polytope's rows and its right
block the second's; the error box plays no part.

## Inputs
* `P₁` – H-polytope
* `P₂` – H-polytope

## Hypotheses
* none

## Conclusion
* the nominal part of `HPolytope.cartProd` is the Cartesian product of the nominal parts
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.cartProd_nominal_exact (P₁ : HPolytope 𝕋 (Vec 𝕋 n₁))
    (P₂ : HPolytope 𝕋 (Vec 𝕋 n₂)) : -- --- CONCL ---
    (P₁.cartProd P₂).nominal.construct
      = blockLeft n₁ n₂ ⁻¹' P₁.nominal.construct
        ∩ blockRight n₁ n₂ ⁻¹' P₂.nominal.construct := by -- --- PROOF ---
  ext y
  show y ∈ ((P₁.padLeft n₂).stackRows (HPolytope.padRight n₁ P₂)).nominal.construct ↔ _
  rw [HPolytope.mem_stackRows_nominal_iff, HPolytope.mem_padLeft_nominal_iff,
    HPolytope.mem_padRight_nominal_iff]
  exact Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

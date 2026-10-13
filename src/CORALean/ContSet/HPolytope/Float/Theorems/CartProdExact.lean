module

public import CORALean.ContSet.HPolytope.Float.Operations.CartProd
public import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemPadLeftIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemPadRightIff

@[expose] public section

/-!
# `HPolytope.cartProd` is exactly the Cartesian product, over a floating-point scalar

A point of the product is a point whose left block is in `P₁` and whose right block is in `P₂`:
`mem_intersection_iff` splits the stacked rows, and `mem_padLeft_iff` and `mem_padRight_iff`
read each half on its own block.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem HPolytope.aux_mem_cartProd_iff {P₁ : HPolytope 𝕋 (Vec 𝕋 n₁)} {P₂ : HPolytope 𝕋 (Vec 𝕋 n₂)}
    {x : Vec ℝ (n₁ + n₂)} :
    x ∈ (P₁.cartProd P₂).construct
      ↔ blockLeft n₁ n₂ x ∈ P₁.construct ∧ blockRight n₁ n₂ x ∈ P₂.construct := by
  unfold HPolytope.cartProd
  rw [HPolytope.mem_intersection_iff, HPolytope.mem_padLeft_iff, HPolytope.mem_padRight_iff]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.cartProd_exact (P₁ : HPolytope 𝕋 (Vec 𝕋 n₁)) (P₂ : HPolytope 𝕋 (Vec 𝕋 n₂)) :
    (P₁.cartProd P₂).construct
      = blockLeft n₁ n₂ ⁻¹' P₁.construct ∩ blockRight n₁ n₂ ⁻¹' P₂.construct :=
  Set.ext fun _ => HPolytope.aux_mem_cartProd_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

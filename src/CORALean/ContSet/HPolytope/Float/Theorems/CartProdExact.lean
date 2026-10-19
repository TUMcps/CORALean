module

public import CORALean.ContSet.HPolytope.Float.Operations.CartProd
public import CORALean.ContSet.HPolytope.Float.Theorems.CartProdNominalExact
public import CORALean.ContSet.HPolytope.Float.Theorems.PreimageAddImage

@[expose] public section

/-!
# `HPolytope.cartProd` is exactly the Cartesian product, over a floating-point scalar

A point of the product is a point whose left block is in `P₁` and whose right block is in `P₂`:
`mem_stackRows_nominal_iff` splits the stacked rows, and `mem_padLeft_nominal_iff` and
`mem_padRight_nominal_iff` read each half on its own block. The error box is the two boxes side by
side, and the sum of a product is the product of the sums.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem HPolytope.aux_mem_cartProd_iff {P₁ : HPolytope 𝕋 (Vec 𝕋 n₁)} {P₂ : HPolytope 𝕋 (Vec 𝕋 n₂)}
    {x : Vec ℝ (n₁ + n₂)} : -- --- CONCL ---
    x ∈ (P₁.cartProd P₂).construct
      ↔ blockLeft n₁ n₂ x ∈ P₁.construct
        ∧ blockRight n₁ n₂ x ∈ P₂.construct := by -- --- PROOF ---
  -- the two blocks, as one map into a product
  let L : Vec ℝ (n₁ + n₂) →+ Vec ℝ n₁ × Vec ℝ n₂ :=
    ((blockLeft n₁ n₂).prod (blockRight n₁ n₂)).toAddMonoidHom
  let S : Vec ℝ n₁ × Vec ℝ n₂ →+ Vec ℝ (n₁ + n₂) :=
    { toFun := fun p => Fin.append p.1 p.2
      map_zero' := by
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
      map_add' := fun p q => by
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp }
  -- the nominal parts multiply
  have hN : (P₁.cartProd P₂).nominal.construct
      = L ⁻¹' (P₁.nominal.construct ×ˢ P₂.nominal.construct) :=
    HPolytope.cartProd_nominal_exact P₁ P₂
  -- and so do the boxes
  have hE : (P₁.cartProd P₂).I_error.construct
      = S '' (P₁.I_error.construct ×ˢ P₂.I_error.construct) := by
    ext y
    constructor
    -- a point of the stacked box splits into its two blocks
    · intro hy
      have hy' := Interval.mem_vec_iff.mp hy
      refine ⟨(blockLeft n₁ n₂ y, blockRight n₁ n₂ y), ⟨Interval.mem_vec_iff.mpr fun j => ?_,
        Interval.mem_vec_iff.mpr fun j => ?_⟩, funext fun j => ?_⟩
      · have h := hy' (Fin.castAdd n₂ j)
        simp only [HPolytope.cartProd, Fin.append_left] at h
        exact h
      · have h := hy' (Fin.natAdd n₁ j)
        simp only [HPolytope.cartProd, Fin.append_right] at h
        exact h
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [S, blockLeft, blockRight]
    -- and two points of the boxes stack
    · rintro ⟨⟨e₁, e₂⟩, ⟨h₁, h₂⟩, rfl⟩
      refine Interval.mem_vec_iff.mpr fun j => ?_
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa [HPolytope.cartProd, S] using Interval.mem_vec_iff.mp h₁ i
      · simpa [HPolytope.cartProd, S] using Interval.mem_vec_iff.mp h₂ i
  have key := HPolytope.preimage_inter_add_image L S
    (fun e => Prod.ext (blockLeft_append e.1 e.2) (blockRight_append e.1 e.2))
    (P₁.nominal.construct ×ˢ P₂.nominal.construct) (P₁.I_error.construct ×ˢ P₂.I_error.construct)
    Set.univ (fun _ _ => by simp)
  simp only [Set.inter_univ, Set.prod_add_prod_comm] at key
  show x ∈ (P₁.cartProd P₂).nominal.construct + (P₁.cartProd P₂).I_error.construct ↔ _
  rw [hN, hE]
  refine (Set.ext_iff.mp key x).trans ?_
  simp only [Set.mem_preimage, Set.mem_prod]
  exact Iff.rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.cartProd_exact (P₁ : HPolytope 𝕋 (Vec 𝕋 n₁)) (P₂ : HPolytope 𝕋 (Vec 𝕋 n₂)) :
    (P₁.cartProd P₂).construct
      = blockLeft n₁ n₂ ⁻¹' P₁.construct ∩ blockRight n₁ n₂ ⁻¹' P₂.construct :=
  Set.ext fun _ => HPolytope.aux_mem_cartProd_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

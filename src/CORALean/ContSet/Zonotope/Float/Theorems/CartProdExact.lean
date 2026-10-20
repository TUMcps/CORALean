module

public import CORALean.ContSet.Zonotope.Float.Operations.CartProd
public import CORALean.ContSet.Zonotope.Real.Theorems.CartProdExact
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.Global.AppendLinear
public import CORALean.ContSet.Zonotope.Float.Theorems.NominalCartProdC
public import CORALean.ContSet.Zonotope.Float.Theorems.NominalCartProdG
public import CORALean.ContSet.InflatedContSet.Theorems.AppendConstruct

@[expose] public section

/-!
# `Zonotope.cartProd` is exact

The stored operands' sets, paired and read through `Fin.append`, are the product's set. Nothing
rounds: the nominal part is the exact layer's `cartProd` mapped through the two block paddings,
and the error box is the product of the two boxes.

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope

## Hypotheses
* none

## Conclusion
* product set equals the paired sets of the operands
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The nominal zonotope of the product is the exact product, mapped through the append. -/
theorem Zonotope.aux_nominal_cartProd (Z₁ : Zonotope (Vec 𝕋 n₁))
    (Z₂ : Zonotope (Vec 𝕋 n₂)) : -- --- CONCL ---
    InflatedContSet.nominal (Z₁.cartProd Z₂) =
      (Real.Zonotope.map (appendLinear n₁ n₂)
        (Real.Zonotope.cartProd (InflatedContSet.nominal Z₁)
          (InflatedContSet.nominal Z₂))) := by -- --- PROOF ---
  show (⟨_, _, _⟩ : Real.Zonotope (Vec ℝ (n₁ + n₂))) = ⟨_, _, _⟩
  congr 1
  · exact Zonotope.nominal_cartProd_c Z₁ Z₂
  · funext j
    exact Zonotope.nominal_cartProd_G Z₁ Z₂ j


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cartProd_exact (Z₁ : Zonotope (Vec 𝕋 n₁))
    (Z₂ : Zonotope (Vec 𝕋 n₂)) : -- --- CONCL ---
    (Z₁.cartProd Z₂).construct = (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
      (Z₁.construct ×ˢ Z₂.construct) := by -- --- PROOF ---
  -- the nominal part: the exact product's set, mapped through the append
  have hN : InflatedContSet.nominalSet (Z₁.cartProd Z₂) =
      (appendLinear n₁ n₂) '' (InflatedContSet.nominalSet Z₁ ×ˢ InflatedContSet.nominalSet Z₂) := by
    unfold InflatedContSet.nominalSet
    rw [Zonotope.aux_nominal_cartProd]
    show (Real.Zonotope.map _ _).construct =
      _ '' (Real.Zonotope.construct _ ×ˢ Real.Zonotope.construct _)
    rw [← Real.Zonotope.map_exact, Real.Zonotope.cartProd_exact]
  -- the error box is the stack of the two, and stacking distributes over the sum
  have hφ : ⇑(appendLinear n₁ n₂) = fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2 :=
    funext appendLinear_apply
  rw [hφ] at hN
  exact CORALean.Float.InflatedContSet.append_construct (s₁ := Z₁) (s₂ := Z₂) hN rfl


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

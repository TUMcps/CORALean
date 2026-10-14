module

public import CORALean.ContSet.ConZonotope.Float.Operations.CartProd
public import CORALean.ContSet.ConZonotope.Real.Theorems.CartProdExact
public import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact
public import CORALean.ContSet.HPolytope.Float.Theorems.CartProdExact
public import CORALean.ContSet.Zonotope.Float.Theorems.CartProdExact
public import CORALean.ContSet.InflatedContSet.Theorems.AppendConstruct

@[expose] public section

/-!
# `ConZonotope.cartProd` is exact

The stored operands' sets, paired and read through `Fin.append`, are the product's set. Nothing
rounds. The nominal part is the exact layer's `cartProd` mapped through the append: its centre and
generators are `Zonotope.cartProd`'s, and its coefficient polytope has the same points as the
exact product of the two (`HPolytope.cartProd_exact`). The error box is the stack of the two.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.cartProd_exact (cZ₁ : ConZonotope 𝕋 (Vec 𝕋 n₁))
    (cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n₂)) :
    (cZ₁.cartProd cZ₂).construct = (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
      (cZ₁.construct ×ˢ cZ₂.construct) := by -- --- PROOF ---
  -- the zonotope parts, whose nominal centre and generators the product shares
  set Z₁ : Zonotope (Vec 𝕋 n₁) := ⟨cZ₁.h, cZ₁.c, fun j i => cZ₁.G j i, cZ₁.I_error⟩
  set Z₂ : Zonotope (Vec 𝕋 n₂) := ⟨cZ₂.h, cZ₂.c, fun j i => cZ₂.G j i, cZ₂.I_error⟩
  -- the nominal part: the exact product, mapped through the append
  have hN : InflatedContSet.nominalSet (cZ₁.cartProd cZ₂) =
      (appendLinear n₁ n₂) ''
        (InflatedContSet.nominalSet cZ₁ ×ˢ InflatedContSet.nominalSet cZ₂) := by
    unfold InflatedContSet.nominalSet
    show _ = _ '' (Real.ConZonotope.construct _ ×ˢ Real.ConZonotope.construct _)
    rw [Real.ConZonotope.cartProd_exact, Real.ConZonotope.map_exact]
    -- the coefficient polytope has the same points as the exact layer's product
    have hP' : ∀ γ : Vec ℝ (cZ₁.h + cZ₂.h),
        γ ∈ (InflatedContSet.nominal (cZ₁.cartProd cZ₂)).P.construct ↔
          γ ∈ (Real.ConZonotope.map (appendLinear n₁ n₂)
            ((InflatedContSet.nominal cZ₁).cartProd
              (InflatedContSet.nominal cZ₂))).P.construct := by
      intro γ
      show γ ∈ (cZ₁.P.cartProd cZ₂.P).construct ↔ γ ∈ (Real.HPolytope.intersection
        ((InflatedContSet.nominal cZ₁).P.comap (blockLeft cZ₁.h cZ₂.h))
        ((InflatedContSet.nominal cZ₂).P.comap (blockRight cZ₁.h cZ₂.h))).construct
      rw [HPolytope.cartProd_exact, Real.HPolytope.mem_intersection_iff]
      exact Iff.rfl
    -- the centre and the generators are the zonotope product's
    have hc := Zonotope.nominal_cartProd_c Z₁ Z₂
    have hG := fun j => Zonotope.nominal_cartProd_G Z₁ Z₂ j
    ext x
    constructor <;> rintro ⟨γ, hγ, hP, hx⟩
    · refine ⟨γ, hγ, (hP' γ).1 hP, ?_⟩
      rw [hx]
      refine congrArg₂ _ hc (Finset.sum_congr rfl fun j _ => ?_)
      exact congrArg (γ j • ·) (hG j)
    · refine ⟨γ, hγ, (hP' γ).2 hP, ?_⟩
      rw [hx]
      refine congrArg₂ _ hc.symm (Finset.sum_congr rfl fun j _ => ?_)
      exact (congrArg (γ j • ·) (hG j)).symm
  -- the error box is the stack of the two, and stacking distributes over the sum
  have hφ : ⇑(appendLinear n₁ n₂) = fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2 :=
    funext appendLinear_apply
  rw [hφ] at hN
  exact CORALean.Float.InflatedContSet.append_construct (s₁ := cZ₁) (s₂ := cZ₂) hN rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.PolyZonotope.Real.Operations.CubMapMixed
public import CORALean.ContSet.PolyZonotope.Real.Theorems.CubMapDepOnExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.CartProdExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact

@[expose] public section

/-!
# `PolyZonotope.cubMapMixed` is exact

The result is exactly the image of the three sets taken independently,
`{ (x₁ᵀ T x₂) * x₃ | x₁ ∈ pZ₁, x₂ ∈ pZ₂, x₃ ∈ pZ₃ }`, each argument ranging over its own set.
The triple is read as `((x₁, x₂), x₃)`, the shape of the nested `cartProd`.

## Inputs
* `T` – family of cubic form tensors
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `pZ₃` – third polynomial zonotope

## Hypotheses
* none

## Conclusion
* the mixed cubic image of the product equals the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.cubMapMixed_exact (T : Fin m → Fin n → Mat ℝ n n)
    (pZ₁ pZ₂ pZ₃ : PolyZonotope (Vec ℝ n)) : -- --- CONCL ---
    (fun x : (Vec ℝ n × Vec ℝ n) × Vec ℝ n => cubEvalMixed T x.1.1 x.1.2 x.2)
        '' ((pZ₁.construct ×ˢ pZ₂.construct) ×ˢ pZ₃.construct)
      = (cubMapMixed T pZ₁ pZ₂ pZ₃).construct := by -- --- PROOF ---
  set P := (pZ₁.dependent.cartProd pZ₂.dependent).cartProd pZ₃.dependent with hP
  -- with nothing independent left, the product set is exactly its points
  have hc : P.construct = P.point '' {a : Fin P.p → ℝ | ∀ k, |a k| ≤ 1} := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := PolyZonotope.exists_point_of_q_zero P rfl hx
      exact ⟨a, ha, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact PolyZonotope.point_mem_construct P ha
  -- and the product set is the three sets, none of them having lost anything
  have hprod : (pZ₁.construct ×ˢ pZ₂.construct) ×ˢ pZ₃.construct = P.construct := by
    rw [hP, ← PolyZonotope.cartProd_exact, ← PolyZonotope.cartProd_exact,
      pZ₁.dependent_exact, pZ₂.dependent_exact, pZ₃.dependent_exact]
  rw [hprod, hc, ← Set.image_comp]
  exact PolyZonotope.cubMapDepOn_exact
    ((LinearMap.fst ℝ (Vec ℝ n) (Vec ℝ n)).comp (LinearMap.fst ℝ (Vec ℝ n × Vec ℝ n) (Vec ℝ n)))
    ((LinearMap.snd ℝ (Vec ℝ n) (Vec ℝ n)).comp (LinearMap.fst ℝ (Vec ℝ n × Vec ℝ n) (Vec ℝ n)))
    (LinearMap.snd ℝ (Vec ℝ n × Vec ℝ n) (Vec ℝ n)) T P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

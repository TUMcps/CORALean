module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Real.Operations.CartProd
public import CORALean.ContSet.Zonotope.Real.Theorems.CartProdExact
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `ZonoBundle.cartProd` is exactly the Cartesian product

`(⋂ i, Aᵢ) ×ˢ (⋂ j, Bⱼ) = ⋂ (i, j), Aᵢ ×ˢ Bⱼ` needs both families nonempty: over an empty
family the left intersection is `univ` while the pairs over a half-empty index are none, so
the statement assumes `0 < k` for both bundles, as CORA's bundles always have.

## Inputs
* `zB₁` – first bundle
* `zB₂` – second bundle

## Hypotheses
* `h₁` – first bundle has a member
* `h₂` – second bundle has a member

## Conclusion
* the product of the two sets is the set of the product
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.cartProd_exact (zB₁ : ZonoBundle α) (zB₂ : ZonoBundle β)
    (h₁ : 0 < zB₁.k) (h₂ : 0 < zB₂.k) :
    zB₁.construct ×ˢ zB₂.construct = (zB₁.cartProd zB₂).construct := by -- --- PROOF ---
  ext ⟨x, y⟩
  simp only [ZonoBundle.construct_eq_iInter, ZonoBundle.cartProd, Set.mem_prod, Set.mem_iInter,
    ← Zonotope.cartProd_exact]
  constructor
  · rintro ⟨hx, hy⟩ p
    exact ⟨hx _, hy _⟩
  · intro h
    exact ⟨fun i => by simpa using (h (finProdFinEquiv (i, ⟨0, h₂⟩))).1,
           fun j => by simpa using (h (finProdFinEquiv (⟨0, h₁⟩, j))).2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

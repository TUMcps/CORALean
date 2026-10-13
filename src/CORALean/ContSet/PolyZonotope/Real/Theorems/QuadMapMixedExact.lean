import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapMixed
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.CartProdExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

/-!
# `quadMapMixed` is exactly the pairing over two independent ranges

Unlike `bilin`, whose claim is about the evaluation map because its two operands
share their factors, this one is a claim about the two *sets*: the result is
exactly the image of `pZ₁.construct ×ˢ pZ₂.construct` under `(x₁, x₂) ↦ x₁ᵀQx₂`.
That is what the Cartesian product is there to buy, `[1, Prop. 11]` being exact.

Three steps, each exact on its own: `dependent_exact` empties the independent
blocks, `cartProd_exact` turns the pair of sets into the product set, and
`bilin_exact` pairs the product with itself over the product's own factors. The
last needs the product's independent block to be empty, which the first supplies
and `cartProd` preserves, so `construct` and the image of `point` coincide there.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The result is exactly the pairwise image, the two arguments ranging over
their own sets independently. -/
theorem PolyZonotope.quadMapMixed_exact (Q : Fin m → Mat ℝ n n)
    (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) :
    (fun x : Vec ℝ n × Vec ℝ n => PolyZonotope.quadBilin Q x.1 x.2)
        '' (pZ₁.construct ×ˢ pZ₂.construct)
      = (PolyZonotope.quadMapMixed Q pZ₁ pZ₂).construct := by -- --- PROOF ---
  -- with nothing independent left, the product set is exactly its points
  have hc : (pZ₁.dependent.cartProd pZ₂.dependent).construct
      = (pZ₁.dependent.cartProd pZ₂.dependent).point
          '' {a : Fin (pZ₁.dependent.cartProd pZ₂.dependent).p → ℝ | ∀ k, |a k| ≤ 1} := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      obtain ⟨a, ha, rfl⟩ :=
        PolyZonotope.exists_point_of_q_zero (pZ₁.dependent.cartProd pZ₂.dependent) rfl hx
      exact ⟨a, ha, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact PolyZonotope.point_mem_construct _ ha
  -- and the product set is the pair of sets, neither operand having lost anything
  have hprod : pZ₁.construct ×ˢ pZ₂.construct
      = (pZ₁.dependent.cartProd pZ₂.dependent).construct := by
    rw [pZ₁.dependent_exact, pZ₂.dependent_exact]
    exact PolyZonotope.cartProd_exact _ _
  rw [hprod, hc, ← Set.image_comp]
  exact PolyZonotope.bilin_exact
    ((PolyZonotope.quadBilin Q).compl₁₂
      (LinearMap.fst ℝ (Vec ℝ n) (Vec ℝ n)) (LinearMap.snd ℝ (Vec ℝ n) (Vec ℝ n)))
    (pZ₁.dependent.cartProd pZ₂.dependent) (pZ₁.dependent.cartProd pZ₂.dependent) rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

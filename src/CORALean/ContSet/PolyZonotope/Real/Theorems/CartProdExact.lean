module

public import CORALean.ContSet.PolyZonotope.Real.Operations.CartProd
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Prod

@[expose] public section

/-!
# `PolyZonotope.cartProd` is exactly the Cartesian product

The result is [1, Prop. 11]. The witnesses are `Fin.append a₁ a₂` and `Fin.append β₁ β₂` on
the factors and the independent coefficients, as in `plus_exact`: the block-diagonal exponent
matrix reads a generator's monomial back as a monomial of its own set alone. A generator of
one set already sits at zero in the other coordinate, so the assembled sum splits along
`Prod.fst`/`Prod.snd` into the two sets' own sums.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* none

## Conclusion
* result equals the Cartesian product of the sets

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] [Module ℝ β] in
/-- `Fin.sum_univ_add` at `cartProd`'s dependent generator count, stated through
the projection because that is the form the goal has and simp will not rewrite
a binder's type. -/
private theorem PolyZonotope.aux_sum_univ_cartProd_h {pZ₁ : PolyZonotope α} {pZ₂ : PolyZonotope β}
    (f : Fin (pZ₁.h + pZ₂.h) → α × β) :
    ∑ i : Fin (pZ₁.cartProd pZ₂).h, f i
      = ∑ i, f (Fin.castAdd pZ₂.h i) + ∑ i, f (Fin.natAdd pZ₁.h i) :=
  Fin.sum_univ_add f

omit [Module ℝ α] [Module ℝ β] in
/-- The same at the independent generator count. -/
private theorem PolyZonotope.aux_sum_univ_cartProd_q {pZ₁ : PolyZonotope α} {pZ₂ : PolyZonotope β}
    (f : Fin (pZ₁.q + pZ₂.q) → α × β) :
    ∑ j : Fin (pZ₁.cartProd pZ₂).q, f j
      = ∑ j, f (Fin.castAdd pZ₂.q j) + ∑ j, f (Fin.natAdd pZ₁.q j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.cartProd_exact (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β) : -- --- CONCL ---
    pZ₁.construct ×ˢ pZ₂.construct = (pZ₁.cartProd pZ₂).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro ⟨x₁, x₂⟩ ⟨⟨a₁, β₁, ha₁, hβ₁, hx₁⟩, ⟨a₂, β₂, ha₂, hβ₂, hx₂⟩⟩
    refine ⟨Fin.append a₁ a₂, Fin.append β₁ β₂,
      Fin.addCases (fun k => by simpa using ha₁ k) (fun k => by simpa using ha₂ k),
      Fin.addCases (fun j => by simpa using hβ₁ j) (fun j => by simpa using hβ₂ j), ?_⟩
    rw [PolyZonotope.aux_sum_univ_cartProd_h, PolyZonotope.aux_sum_univ_cartProd_q]
    simp only [PolyZonotope.cartProd, PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
    refine Prod.ext ?_ ?_
    · simpa only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero,
        add_zero] using hx₁
    · simpa only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero,
        zero_add] using hx₂
  -- back: the pair's own equation, read off each coordinate
  · rintro ⟨x₁, x₂⟩ ⟨a, β, ha, hβ, hxy⟩
    have hx₁ : x₁ = pZ₁.c + ∑ i, PolyZonotope.monomial pZ₁.E (fun k => a (Fin.castAdd pZ₂.p k)) i
              • pZ₁.G i + ∑ j, β (Fin.castAdd pZ₂.q j) • pZ₁.GI j := by
      have h1 := congrArg Prod.fst hxy
      rw [PolyZonotope.aux_sum_univ_cartProd_h, PolyZonotope.aux_sum_univ_cartProd_q] at h1
      simpa only [PolyZonotope.cartProd, PolyZonotope.monomial_plusE_left,
        PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right, Prod.fst_add,
        Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero, add_zero] using h1
    have hx₂ : x₂ = pZ₂.c + ∑ i, PolyZonotope.monomial pZ₂.E (fun k => a (Fin.natAdd pZ₁.p k)) i
              • pZ₂.G i + ∑ j, β (Fin.natAdd pZ₁.q j) • pZ₂.GI j := by
      have h2 := congrArg Prod.snd hxy
      rw [PolyZonotope.aux_sum_univ_cartProd_h, PolyZonotope.aux_sum_univ_cartProd_q] at h2
      simpa only [PolyZonotope.cartProd, PolyZonotope.monomial_plusE_left,
        PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right, Prod.snd_add,
        Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero, zero_add] using h2
    exact ⟨⟨fun k => a (Fin.castAdd pZ₂.p k), fun j => β (Fin.castAdd pZ₂.q j),
              fun k => ha _, fun j => hβ _, hx₁⟩,
           ⟨fun k => a (Fin.natAdd pZ₁.p k), fun j => β (Fin.natAdd pZ₁.q j),
              fun k => ha _, fun j => hβ _, hx₂⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

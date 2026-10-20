module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ExactPlus
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# `exactPlus` is the sum over shared factors

What [1, Prop. 10] calls exactness: `construct (exactPlus pZ₁ pZ₂ hp)` is not
`construct pZ₁ + construct pZ₂`, which `plus` computes and is strictly larger. Both sets are
functions of one shared factor vector, so the claim is about the evaluation map: the result's
point at `a` is the sum of the two sets' points at that same `a`, with `pZ₂` read through
`Fin.cast`, as `mul_point` states it for a product. The independent blocks take no part:
`point` ignores them. The only thing Prop. 10 changes about `plus` is the exponent matrix.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `a` – factor values

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* the point is the sum of the two points

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at the generator count `exactPlus` produces, the binder
ascribed so that it matches the goal. -/
theorem PolyZonotope.aux_sum_univ_exactPlus {pZ₁ pZ₂ : PolyZonotope α} {hp : pZ₁.p = pZ₂.p}
    (f : Fin (pZ₁.h + pZ₂.h) → α) :
    ∑ l : Fin (pZ₁.exactPlus pZ₂ hp).h, f l
      = ∑ i, f (Fin.castAdd pZ₂.h i) + ∑ j, f (Fin.natAdd pZ₁.h j) :=
  Fin.sum_univ_add f

omit [Module ℝ α] in
/-- A column from the left operand keeps its own monomial, the appended columns
standing to its right. -/
theorem PolyZonotope.aux_monomial_exactPlus_left (pZ₁ pZ₂ : PolyZonotope α)
    (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ) (i : Fin pZ₁.h) :
    monomial (pZ₁.exactPlus pZ₂ hp).E a (Fin.castAdd pZ₂.h i) = monomial pZ₁.E a i :=
  Finset.prod_congr rfl fun k _ => by rw [show (pZ₁.exactPlus pZ₂ hp).E k (Fin.castAdd pZ₂.h i)
    = pZ₁.E k i from Fin.append_left _ _ i]

omit [Module ℝ α] in
/-- A column from the right operand keeps its own monomial, read at `pZ₂`'s
factor indices: the two products run over one factor set renamed. -/
theorem PolyZonotope.aux_monomial_exactPlus_right (pZ₁ pZ₂ : PolyZonotope α)
    (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ) (i : Fin pZ₂.h) : -- --- CONCL ---
    monomial (pZ₁.exactPlus pZ₂ hp).E a (Fin.natAdd pZ₁.h i)
      = monomial pZ₂.E (fun k => a (Fin.cast hp.symm k)) i := by -- --- PROOF ---
  show ∏ k, a k ^ (pZ₁.exactPlus pZ₂ hp).E k (Fin.natAdd pZ₁.h i)
      = ∏ k, a (Fin.cast hp.symm k) ^ pZ₂.E k i
  -- the appended half is `pZ₂`'s own column, at `pZ₁`'s factor index
  have hcol : ∀ k, (pZ₁.exactPlus pZ₂ hp).E k (Fin.natAdd pZ₁.h i)
      = pZ₂.E (Fin.cast hp k) i := fun k => Fin.append_right _ _ i
  rw [Finset.prod_congr rfl fun k _ => by rw [hcol k]]
  exact Fintype.prod_equiv (finCongr hp) _ _ fun _ => rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- `exactPlus`'s point: the two sets' points at the same factor vector, added. -/
theorem PolyZonotope.exactPlus_point (pZ₁ pZ₂ : PolyZonotope α) (hp : pZ₁.p = pZ₂.p)
    (a : Fin pZ₁.p → ℝ) : -- --- CONCL ---
    (pZ₁.exactPlus pZ₂ hp).point a
      = pZ₁.point a + pZ₂.point (fun k => a (Fin.cast hp.symm k)) := by -- --- PROOF ---
  simp only [PolyZonotope.point]
  rw [PolyZonotope.aux_sum_univ_exactPlus]
  -- each half's monomials first, while they are still stated at `exactPlus`'s matrix
  simp only [PolyZonotope.aux_monomial_exactPlus_left, PolyZonotope.aux_monomial_exactPlus_right]
  simp only [PolyZonotope.exactPlus, Fin.append_left, Fin.append_right]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

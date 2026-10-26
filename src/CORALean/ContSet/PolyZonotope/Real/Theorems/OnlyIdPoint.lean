module

public import CORALean.ContSet.PolyZonotope.Real.Operations.OnlyId
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point

@[expose] public section

/-!
# `PolyZonotope.onlyId` splits the point exactly

At every factor vector the point of `pZ` is the sum of the point of the `S`-part at the factors of
`S` and the point of the remainder: a generator of the first part has exponent `0` outside `S`, so
its monomial reads the factors of `S` only, and every other generator is in the remainder, with
the center `0` there so that the center is counted once. The independent block belongs to the
remainder and is not part of `point`.

## Inputs
* `pZ` – polynomial zonotope
* `S` – selected factors
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the point is the sum of the two parts' points
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- A column with exponent `0` outside `S` has the monomial of the factors of `S` alone. -/
private theorem PolyZonotope.aux_monomial_onlyId (pZ : PolyZonotope α) (S : Finset (Fin pZ.p))
    (a : Fin pZ.p → ℝ) (i : Fin pZ.h) (hi : ∀ k, k ∉ S → pZ.E k i = 0) : -- --- CONCL ---
    PolyZonotope.monomial (pZ.onlyId S).1.E (fun k' => a (S.orderIsoOfFin rfl k').1) i
      = PolyZonotope.monomial pZ.E a i := by -- --- PROOF ---
  unfold PolyZonotope.monomial
  -- the factors outside `S` carry exponent `0`
  rw [← Finset.prod_subset (Finset.subset_univ S) fun k _ hk => by rw [hi k hk, pow_zero],
    ← Finset.prod_coe_sort S]
  exact Equiv.prod_comp (S.orderIsoOfFin rfl).toEquiv fun x => a x ^ pZ.E x i


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.onlyId_point (pZ : PolyZonotope α) (S : Finset (Fin pZ.p))
    (a : Fin pZ.p → ℝ) : -- --- CONCL ---
    pZ.point a = (pZ.onlyId S).1.point (fun k' => a (S.orderIsoOfFin rfl k').1)
      + (pZ.onlyId S).2.point a := by -- --- PROOF ---
  -- each generator is in exactly one of the two parts
  have hsplit : ∀ i, PolyZonotope.monomial pZ.E a i • pZ.G i
      = PolyZonotope.monomial (pZ.onlyId S).1.E (fun k' => a (S.orderIsoOfFin rfl k').1) i
          • (pZ.onlyId S).1.G i
        + PolyZonotope.monomial (pZ.onlyId S).2.E a i • (pZ.onlyId S).2.G i := by
    intro i
    by_cases hi : ∀ k, k ∉ S → pZ.E k i = 0
    · rw [PolyZonotope.aux_monomial_onlyId pZ S a i hi]
      simp [PolyZonotope.onlyId, if_pos hi]
    · simp [PolyZonotope.onlyId, if_neg hi]
  show pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
    = ((pZ.onlyId S).1.c + ∑ i, PolyZonotope.monomial (pZ.onlyId S).1.E
        (fun k' => a (S.orderIsoOfFin rfl k').1) i • (pZ.onlyId S).1.G i)
      + ((pZ.onlyId S).2.c + ∑ i, PolyZonotope.monomial (pZ.onlyId S).2.E a i
        • (pZ.onlyId S).2.G i)
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib]
  -- the remainder's center is `0` and the first part's is `c`
  show pZ.c + _ = (pZ.c + _) + ((0 : α) + _)
  rw [zero_add]
  exact (add_assoc _ _ _).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

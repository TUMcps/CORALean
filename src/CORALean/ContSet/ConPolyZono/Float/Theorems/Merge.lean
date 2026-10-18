module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberEqZeroOfNotMem

@[expose] public section

/-!
# The exact layer's regrouping at this layer's stored columns, exact reals

Shared by both merges: it is stated over an exponent matrix and a matrix of
stored floats and knows nothing about which block they came from, so `A`'s rows
use it as `G`'s do. `E'` is passed rather than computed, so the caller's own
field is what appears in the result.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum over the kept columns, read against a plain count. -/
theorem ConPolyZono.aux_sum_keep {d : ℕ} (t : Finset (Fin d)) (f : Fin d → ℝ) :
    ∑ j ∈ t, f j = ∑ j : Fin t.card, f (t.orderIsoOfFin rfl j) := by
  rw [← Finset.sum_coe_sort t f]
  exact (Equiv.sum_comp (t.orderIsoOfFin rfl).toEquiv fun x => f x).symm


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exact layer's regrouping at this layer's stored columns, which are exact
reals. `E'` is passed rather than computed, so the caller's own field is what
appears in the result. -/
theorem ConPolyZono.merge {p d h : ℕ} (E : Fin p → Fin h → ℕ) (G : Mat 𝕋 d h)
    (a : Fin p → ℝ) (E' : Fin p → Fin (PolyZonotope.repKeep E).card → ℕ)
    (hE' : ∀ k j, E' k j = E k (PolyZonotope.keepIdx E j)) (i : Fin d) : -- --- STMT ---
    (∑ l, toReal (G i l) * Real.PolyZonotope.monomial E a l)
      = ∑ j : Fin (PolyZonotope.repKeep E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep E)
              (fun l => toReal (G i l)) (PolyZonotope.keepIdx E j)
            * Real.PolyZonotope.monomial E' a j := by -- --- PROOF ---
  have hmon : ∀ j, Real.PolyZonotope.monomial E' a j
      = Real.PolyZonotope.monomial E a (PolyZonotope.keepIdx E j) := fun j => by
    rw [Real.PolyZonotope.monomial, Real.PolyZonotope.monomial]
    exact Finset.prod_congr rfl fun k _ => by rw [hE' k j]
  -- the merge itself is the exact layer's, the stored columns being exact reals
  calc (∑ l, toReal (G i l) * Real.PolyZonotope.monomial E a l)
      = ∑ l, Real.PolyZonotope.monomial E a l • toReal (G i l) :=
        Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul]; exact mul_comm _ _
    _ = ∑ j ∈ PolyZonotope.repKeep E, Real.PolyZonotope.monomial E a j
          • Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep E)
              (fun l => toReal (G i l)) j :=
        Real.PolyZonotope.sum_monomial_merge E (fun l => toReal (G i l)) a
          (Real.PolyZonotope.rep E) (PolyZonotope.repKeep E)
          (Real.PolyZonotope.col_rep E)
          fun j hj => PolyZonotope.fiber_eq_zero_of_notMem E _ hj
    -- and re-indexed by a plain count, which is what the count field takes
    _ = ∑ j : Fin (PolyZonotope.repKeep E).card,
          Real.PolyZonotope.monomial E a (PolyZonotope.keepIdx E j)
            • Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep E)
                (fun l => toReal (G i l)) (PolyZonotope.keepIdx E j) :=
        ConPolyZono.aux_sum_keep _ _
    _ = ∑ j : Fin (PolyZonotope.repKeep E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep E)
              (fun l => toReal (G i l)) (PolyZonotope.keepIdx E j)
            * Real.PolyZonotope.monomial E' a j :=
        Finset.sum_congr rfl fun j _ => by
          rw [smul_eq_mul, hmon j]; exact mul_comm _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

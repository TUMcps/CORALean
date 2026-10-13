import CORALean.ContSet.PolyZonotope.Real.Complexity.Mul
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `PolyZonotope.evalPolySort`'s dependent-generator count

[1, Prop. 3.5 (generators)]: the polynomial evaluation of Alg. 2 "has `O(h^o)` generators", `o` the
degree. `merge` keeps one column per class, so never more than it is given. `sort` permutes. `mul`
has `(h₁ + 1)(h₂ + 1)`. So `PZ^(k+1)` has at most `(h + 2)^(k+1) - 1`, and the sum of the powers
`1..o` at most `o (h + 2)^o`. For `h ≥ 1` that is at most `o 3^o h^o`, a constant in `o` times
`h^o`.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `merge` keeps at most every column. -/
theorem PolyZonotope.aux_merge_h_le {α : Type} [AddCommGroup α] [Module ℝ α]
    (pZ : PolyZonotope α) : pZ.merge.h ≤ pZ.h := by
  show (PolyZonotope.mergeKeep pZ.E).card ≤ pZ.h
  exact (Finset.card_le_univ _).trans (Fintype.card_fin _).le

/-- `PZ^(k+1)`, sorted and merged, has at most `(h + 2)^(k+1) - 1` generators. -/
theorem PolyZonotope.aux_powSort_h_le (pZ : PolyZonotope (Vec ℝ n)) (k : ℕ) :
    (pZ.powSort k).1.h + 1 ≤ (pZ.h + 2) ^ (k + 1) := by -- --- PROOF ---
  induction k with
  | zero => show pZ.h + 1 ≤ (pZ.h + 2) ^ 1; rw [pow_one]; omega
  | succ k ih =>
      -- `merge ∘ sort ∘ mul`: `(R.h + 1)(h + 1)` columns at most
      have hm : (pZ.powSort (k + 1)).1.h
          ≤ ((pZ.powSort k).1.h + 1) * (pZ.h + 1) := by
        show ((((pZ.powSort k).1.mul pZ (pZ.powSort k).2).sort).merge).h ≤ _
        refine (PolyZonotope.aux_merge_h_le _).trans ?_
        show ((pZ.powSort k).1.mul pZ (pZ.powSort k).2).h ≤ _
        rw [PolyZonotope.mul_h]
      have hle : ((pZ.powSort k).1.h + 1) * (pZ.h + 1) ≤ (pZ.h + 2) ^ (k + 1) * (pZ.h + 1) :=
        Nat.mul_le_mul_right _ ih
      have hpos : 1 ≤ (pZ.h + 2) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
      calc (pZ.powSort (k + 1)).1.h + 1
          ≤ (pZ.h + 2) ^ (k + 1) * (pZ.h + 1) + 1 := by omega
        _ ≤ (pZ.h + 2) ^ (k + 1) * (pZ.h + 1) + (pZ.h + 2) ^ (k + 1) := by omega
        _ = (pZ.h + 2) ^ (k + 1 + 1) := by ring

/-- The tail of Alg. 2's sum from degree `k + 1`: at most `Σ_{i < len} (h + 2)^(k+i+1)`. -/
theorem PolyZonotope.aux_evalPolySortTail_h_le (pZ : PolyZonotope (Vec ℝ n))
    (rest : List (Vec ℝ n)) (k : ℕ) :
    (PolyZonotope.evalPolySortTailP pZ rest k).1.h
      ≤ ∑ i ∈ Finset.range rest.length, (pZ.h + 2) ^ (k + i + 1) := by -- --- PROOF ---
  induction rest generalizing k with
  | nil => show 0 ≤ _; exact Nat.zero_le _
  | cons a rest ih =>
      -- `sortPlus` is `merge ∘ sort ∘ exactPlus`, at most the two counts added
      have hsp : (PolyZonotope.evalPolySortTailP pZ (a :: rest) k).1.h
          ≤ (pZ.powSort k).1.h + (PolyZonotope.evalPolySortTailP pZ rest (k + 1)).1.h := by
        show (((((pZ.powSort k).1.map (Entrywise.hadamardLin a)).exactPlus
          (PolyZonotope.evalPolySortTailP pZ rest (k + 1)).1 _).sort).merge).h ≤ _
        exact PolyZonotope.aux_merge_h_le _
      have h1 := PolyZonotope.aux_powSort_h_le pZ k
      have h2 := ih (k + 1)
      rw [List.length_cons, Finset.sum_range_succ']
      have hshift : ∑ i ∈ Finset.range rest.length, (pZ.h + 2) ^ (k + 1 + i + 1)
          = ∑ i ∈ Finset.range rest.length, (pZ.h + 2) ^ (k + (i + 1) + 1) :=
        Finset.sum_congr rfl fun i _ => by ring_nf
      rw [← hshift]
      simp only [add_zero]
      omega


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3.5 (generators)]: Alg. 2 at a polynomial of degree `o` has at most `o · 3^o · h^o`
generators when `h ≥ 1`, which is `O(h^o)`. -/
theorem PolyZonotope.evalPolySort_h_le (pZ : PolyZonotope (Vec ℝ n)) (coeffs : List (Vec ℝ n))
    (hh : 1 ≤ pZ.h) :
    (pZ.evalPolySort coeffs).h
      ≤ (coeffs.length - 1) * 3 ^ (coeffs.length - 1)
        * pZ.h ^ (coeffs.length - 1) := by -- --- PROOF ---
  cases coeffs with
  | nil => exact Nat.zero_le _
  | cons a0 rest =>
      show (PolyZonotope.evalPolySortTailP pZ rest 0).1.h ≤ _
      refine (PolyZonotope.aux_evalPolySortTail_h_le pZ rest 0).trans ?_
      simp only [List.length_cons, Nat.add_sub_cancel, zero_add]
      -- every term is at most `(h + 2)^o ≤ (3h)^o`
      have hterm : ∀ i ∈ Finset.range rest.length,
          (pZ.h + 2) ^ (i + 1) ≤ 3 ^ rest.length * pZ.h ^ rest.length := fun i hi => by
        have hi' : i + 1 ≤ rest.length := Finset.mem_range.mp hi
        calc (pZ.h + 2) ^ (i + 1) ≤ (3 * pZ.h) ^ (i + 1) :=
              Nat.pow_le_pow_left (by omega) _
          _ ≤ (3 * pZ.h) ^ rest.length :=
              Nat.pow_le_pow_right (by omega) hi'
          _ = 3 ^ rest.length * pZ.h ^ rest.length := mul_pow _ _ _
      calc ∑ i ∈ Finset.range rest.length, (pZ.h + 2) ^ (i + 1)
          ≤ ∑ _i ∈ Finset.range rest.length, 3 ^ rest.length * pZ.h ^ rest.length :=
            Finset.sum_le_sum hterm
        _ = rest.length * 3 ^ rest.length * pZ.h ^ rest.length := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_assoc]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

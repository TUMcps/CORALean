import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit

/-!
# `girardSplit` ranks by Girard's metric

The partition `girardSplit` cuts satisfies [1, Eq. (5)]: every kept generator `g_a` and every
dropped one `g_b` have `‖g_a‖₁ - ‖g_a‖∞ ≥ ‖g_b‖₁ - ‖g_b‖∞`.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real
open scoped CORALean
variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. (5)]: the kept generators rank above the dropped ones by `‖g‖₁ - ‖g‖∞`. -/
theorem Zonotope.girardSplit_metric_le (Z : Zonotope (Vec ℝ n)) (o : ℕ) (hlt : o * n < Z.h)
    (l : Fin ((o - 1) * n)) (r : Fin (Z.h - (o - 1) * n)) :
    let m := fun j => (∑ i, |Z.G j i|) - Finset.univ.fold max 0 fun i => |Z.G j i|
    m ((Z.girardSplit o hlt).right r) ≤ m ((Z.girardSplit o hlt).left l) := by -- --- PROOF ---
  intro m
  -- `Tuple.sort` makes the negated metric monotone, and `left` precedes `right`
  have hm := Tuple.monotone_sort
    fun j => -((∑ i, |Z.G j i|) - Finset.univ.fold max 0 fun i => |Z.G j i|)
  have h := @hm (finCongr (Nat.add_sub_cancel' (le_of_lt (lt_of_le_of_lt
    (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt))).symm.symm (Fin.castAdd _ l))
    (finCongr (Nat.add_sub_cancel' (le_of_lt (lt_of_le_of_lt
    (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt))).symm.symm (Fin.natAdd _ r))
    (by simp [Fin.le_def]; omega)
  simp only [Function.comp] at h
  exact neg_le_neg_iff.mp h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

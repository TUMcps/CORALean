import CORALean.ContSet.Zonotope.Real.Operations.ReduceMethC

/-!
# `Zonotope.reduceMethC` bounds the generator count

`reduceByBasis` grows the count exactly as `reduceBy` does — `h := q + n`, one
new generator per column of the basis, the same number a box has — so the
bound is `reduceGirard_order_le`'s and the branch on the determinant costs
nothing: both sides land at `(o-1)*n + n`.

At `o = 0` there is nothing to state, as for Girard's rule and Combastel's:
CORA floors the reduced budget at nothing, so order zero lands at order one.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceMethC_order_le (Z : Zonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (Z.reduceMethC o).h ≤ o * n := by -- --- PROOF ---
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold Zonotope.reduceMethC
  split_ifs with hlt hdet
  · exact le_of_eq hK
  · exact le_of_eq hK
  · exact Nat.le_of_not_lt hlt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

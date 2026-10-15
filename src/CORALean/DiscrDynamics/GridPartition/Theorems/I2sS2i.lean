module

public import CORALean.DiscrDynamics.GridPartition.Operations.Basic

@[expose] public section

/-!
# `i2s` undoes `s2i`

Subscripts in range are recovered from the cell number.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `i2s (s2i sub) = sub` for subscripts in range: `sub2ind` followed by `ind2sub`. -/
theorem GridPartition.i2s_s2i (siz : Fin n → ℕ) {sub : Fin n → ℕ}
    (h : ∀ i, 0 < sub i ∧ sub i ≤ siz i) :
    GridPartition.i2s siz (GridPartition.s2i siz sub) = sub := by -- --- PROOF ---
  funext i
  unfold GridPartition.s2i
  rw [if_pos h]
  let f : (i : Fin n) → Fin (siz i) := fun i => ⟨sub i - 1, by have := h i; omega⟩
  have key3 := congrArg Fin.val (congrFun ((finPiFinEquiv (n := siz)).symm_apply_apply f) i)
  have hs : ∑ i, (sub i - 1) * GridPartition.multiplicator siz i + 1 - 1 =
      (finPiFinEquiv f).val := by
    rw [finPiFinEquiv_apply]; rfl
  have hi := h i
  unfold GridPartition.i2s
  rw [hs]
  have : ((finPiFinEquiv (n := siz)).symm (finPiFinEquiv f) i).val =
      (finPiFinEquiv f).val / GridPartition.multiplicator siz i % siz i := rfl
  rw [← this, key3]
  show sub i - 1 + 1 = sub i
  omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

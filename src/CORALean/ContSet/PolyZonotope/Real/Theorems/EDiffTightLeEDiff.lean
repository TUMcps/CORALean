module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiffTight

@[expose] public section

/-!
# `eDiffTight` is at most `eDiff`

The tightening of [1, Prop. 3] is real: `eDiff` bounds the maximum by `0`, `1` or `2` from the
parity alone, and the maximum itself is `0` and `2` where those are exact and below `1` where
`eDiff` says `1`, the equal-parity exponents that differ. `abs_sub_pow_le_eDiffTight` says it is
still an upper bound.
## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The maximum is at most the parity bound. -/
theorem PolyZonotope.eDiffTight_le_eDiff (a b : ℕ) :
    PolyZonotope.eDiffTight a b ≤ (PolyZonotope.eDiff a b : ℝ) := by -- --- PROOF ---
  unfold PolyZonotope.eDiffTight PolyZonotope.eDiff
  by_cases hab : a = b
  · simp [hab]
  by_cases hp : a % 2 = b % 2
  · -- equal parity, `eDiff` is `1`: the closed form is a product of factors at most one
    rw [if_neg hab, if_neg hab, if_pos hp, if_neg (not_not.mpr hp), Nat.cast_one]
    dsimp only
    split_ifs with hl
    · exact le_rfl
    · have hh : (0 : ℝ) < (max a b : ℕ) := by
        have : 0 < max a b := lt_of_lt_of_le (Nat.pos_of_ne_zero hl) (min_le_max)
        exact_mod_cast this
      refine mul_le_one₀ (Real.rpow_le_one (by positivity) ?_ (by positivity)) (by positivity) ?_
      · exact div_le_one_of_le₀ (Nat.cast_le.mpr min_le_max) hh.le
      · exact div_le_one_of_le₀ (Nat.cast_le.mpr (Nat.sub_le _ _)) hh.le
  · -- different parity: both are `2`
    rw [if_neg hab, if_neg hab, if_neg hp, if_pos hp]
    norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Zonotope.Real.Operations.Dcos

@[expose] public section

/-!
# [1, Eq. (4)] is the cosine when both first elements are nonzero

The corrected statement: for generators whose first elements are both nonzero,
`sign(gᵢ(1) gⱼ(1)) = sign(gᵢ(1)) sign(gⱼ(1))`, and (4) is the cosine of the angle between
`sign(gᵢ(1))gᵢ` and `sign(gⱼ(1))gⱼ`. `exists_dcos_ne_cosSigned` is the case it misses.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real
open scoped CORALean
variable {n : ℕ} [NeZero n]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. (4)] is the cosine of the sign-aligned generators away from a zero first element. -/
theorem Zonotope.dcos_eq_cosSigned (gi gj : Vec ℝ n) (hi : gi 0 ≠ 0)
    (hj : gj 0 ≠ 0) : -- --- STMT ---
    Zonotope.dcos gi gj =
      dotProduct ((if gi 0 < 0 then (-1 : ℝ) else 1) • gi) ((if gj 0 < 0 then (-1 : ℝ) else 1) • gj)
        / (‖(if gi 0 < 0 then (-1 : ℝ) else 1) • gi‖₂ * ‖(if gj 0 < 0 then (-1 : ℝ) else 1) • gj‖₂)
    := by -- --- PROOF ---
  -- a sign `s` with `s² = 1` leaves the 2-norm alone
  have hn : ∀ (s : ℝ) (x : Vec ℝ n), s ^ 2 = 1 → ‖s • x‖₂ = ‖x‖₂ := fun s x h => by
    simp only [norm₂, Pi.smul_apply, smul_eq_mul, mul_pow, h, one_mul]
  have hsq : ∀ x : Vec ℝ n, dotProduct x x = ∑ i, x i ^ 2 := fun x => by simp [dotProduct, sq]
  have hs : ∀ x : ℝ, (if x < 0 then (-1 : ℝ) else 1) ^ 2 = 1 := fun x => by split_ifs <;> norm_num
  rw [hn _ _ (hs _), hn _ _ (hs _), Zonotope.dcos, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, hsq, hsq, norm₂, norm₂,
    ← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  -- the product's sign is the product of the signs, as neither is zero
  have hsign : (if gi 0 * gj 0 < 0 then (-1 : ℝ) else 1)
      = (if gi 0 < 0 then -1 else 1) * (if gj 0 < 0 then -1 else 1) := by
    rcases lt_or_gt_of_ne hi with h1 | h1 <;> rcases lt_or_gt_of_ne hj with h2 | h2
    · simp [h1, h2, not_lt.mpr (mul_pos_of_neg_of_neg h1 h2).le]
    · simp [h1, not_lt.mpr h2.le, mul_neg_of_neg_of_pos h1 h2]
    · simp [h2, not_lt.mpr h1.le, mul_neg_of_pos_of_neg h1 h2]
    · simp [not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr (mul_pos h1 h2).le]
  rw [hsign]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

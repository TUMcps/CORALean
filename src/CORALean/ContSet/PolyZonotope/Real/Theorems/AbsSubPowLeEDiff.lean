module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff

@[expose] public section

/-!
# `eDiff` bounds the difference of two powers on `[-1,1]`

The one fact the exponent relaxation rests on, `[1, Prop. 3]` as an inequality rather than as
a maximum: the two monomials share every factor but one, so their difference is `(x^a - x^b)`
times a product that never leaves `[-1,1]`. Equal parity is where the bound is worth having:
`a = 2s + r` and `b = 2t + r` share the remainder, so both powers are `x^r` times a power of
`x²`, which stays in `[0,1]`, where two powers differ by at most one. Without it, `x^a` and
`x^b` land on opposite sides of zero at `x = -1` and the bound is the trivial `2`.

## Inputs
* `x` – real number
* `a` – first exponent
* `b` – second exponent

## Hypotheses
* `hx` – number is at most one in absolute value

## Conclusion
* the powers differ by at most the exponent difference

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Powers of `x²`, the shape both powers take once their common parity
remainder is split off. -/
theorem PolyZonotope.aux_sq_pow_mem {x : ℝ} (hx : |x| ≤ 1) (m : ℕ) :
    0 ≤ (x ^ 2) ^ m ∧ (x ^ 2) ^ m ≤ 1 := by
  have hsq : x ^ 2 ≤ 1 := by
    have h : |x| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
    rwa [← abs_pow, abs_of_nonneg (sq_nonneg x)] at h
  exact ⟨pow_nonneg (sq_nonneg x) m, pow_le_one₀ (sq_nonneg x) hsq⟩

/-- Two powers of equal parity differ by at most one on `[-1,1]`. -/
theorem PolyZonotope.aux_abs_sub_pow_le_one {x : ℝ} (hx : |x| ≤ 1) {a b : ℕ}
    (hab : a % 2 = b % 2) : |x ^ a - x ^ b| ≤ 1 := by -- --- PROOF ---
  -- a power splits into a power of `x²` and the parity remainder
  have hsplit : ∀ m : ℕ, x ^ m = (x ^ 2) ^ (m / 2) * x ^ (m % 2) := fun m => by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [hsplit a, hsplit b, hab, ← sub_mul, abs_mul]
  refine mul_le_one₀ ?_ (abs_nonneg _) ?_
  · rw [abs_le]
    exact ⟨by linarith [(PolyZonotope.aux_sq_pow_mem hx (a / 2)).1,
        (PolyZonotope.aux_sq_pow_mem hx (b / 2)).2],
      by linarith [(PolyZonotope.aux_sq_pow_mem hx (a / 2)).2,
        (PolyZonotope.aux_sq_pow_mem hx (b / 2)).1]⟩
  · rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) hx


-- =======================================  MAIN THEOREM  ======================================= --

/-- `eDiff` bounds the difference of two powers of a factor in `[-1,1]`. -/
theorem PolyZonotope.abs_sub_pow_le_eDiff {x : ℝ} (hx : |x| ≤ 1) (a b : ℕ) :
    |x ^ a - x ^ b| ≤ (PolyZonotope.eDiff a b : ℝ) := by -- --- PROOF ---
  rw [PolyZonotope.eDiff]
  split_ifs with hab hpar
  · rw [hab, sub_self, abs_zero, Nat.cast_zero]
  · rw [Nat.cast_one]
    exact PolyZonotope.aux_abs_sub_pow_le_one hx hpar
  -- differing parity: nothing is shared, and each power alone stays in `[-1,1]`
  · have h : ∀ m : ℕ, |x ^ m| ≤ 1 := fun m => by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg x) hx
    have hle : |x ^ a - x ^ b| ≤ |x ^ a| + |x ^ b| := by
      rw [sub_eq_add_neg, ← abs_neg (x ^ b)]
      exact abs_add_le _ _
    rw [Nat.cast_ofNat]
    linarith [h a, h b]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# When one power of a factor never exceeds another on `[-1,1]`

The sign half of what `eDiff` bounds in absolute value: `abs_sub_pow_le_eDiff` says how far
`α^A` and `α^B` drift apart, and this says when the drift has only one direction. Two
disjuncts, `[1, Def. 5]`'s parity condition: `B = 0` leaves `α^A - 1`, nonpositive because
`|α| ≤ 1`; and `A` and `B` both even makes both powers powers of `α² ∈ [0,1]`, where the higher
exponent gives the smaller value. Neither asks anything of the other exponent's parity.

## Inputs
* `x` – real number
* `A` – first exponent
* `B` – second exponent

## Hypotheses
* `hx` – number is at most one in absolute value
* `hcase` – second is zero or both even and ordered

## Conclusion
* the first power does not exceed the second

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `α^A ≤ α^B` on `[-1,1]` when `B` is zero, or when both are even and `B` is
the smaller. -/
theorem PolyZonotope.sub_pow_nonpos {x : ℝ} (hx : |x| ≤ 1) {A B : ℕ}
    (hcase : B = 0 ∨ (Even A ∧ Even B ∧ B ≤ A)) : x ^ A - x ^ B ≤ 0 := by -- --- PROOF ---
  rcases hcase with hB | ⟨hA, hB, hle⟩
  -- against the empty product, every power of a factor in `[-1,1]` is below one
  · have habs : |x ^ A| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg x) hx
    rw [hB, pow_zero]
    linarith [(abs_le.mp habs).2]
  -- both even: powers of `α²`, which stays in `[0,1]`
  · obtain ⟨s, hs⟩ := hA
    obtain ⟨t, ht⟩ := hB
    have hy1 : x ^ 2 ≤ 1 := by
      have h : |x| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
      rwa [← abs_pow, abs_of_nonneg (sq_nonneg x)] at h
    have hts : t ≤ s := by omega
    have hpow : (x ^ 2) ^ s ≤ (x ^ 2) ^ t := pow_le_pow_of_le_one (sq_nonneg x) hy1 hts
    rw [hs, ht, ← two_mul, ← two_mul, pow_mul, pow_mul]
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

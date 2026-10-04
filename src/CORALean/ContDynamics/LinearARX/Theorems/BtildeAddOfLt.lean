import CORALean.ContDynamics.LinearARX.Theorems.BextEqZero
import CORALean.ContDynamics.LinearARX.Operations.Btilde

/-!
# Settled parameters

[1, Lemma 2]: for `i < k`, `B̃ᵢ(k+Δk) = B̃ᵢ(k)`. The terms `j ≥ k` that `k + Δk` adds
to (9b) of [1, Thm. 1] carry `B̄_ext,i-j` with `i - j < 0`, which is zero.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.Btilde_add_of_lt (sys : LinearARX 𝕋 dy du p) (k Δk : ℕ) {i : ℤ}
    (hi : i < k) : sys.Btilde (k + Δk) i = sys.Btilde k i := by
  unfold LinearARX.Btilde
  rw [Finset.sum_range_add, add_eq_left]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [sys.Bext_eq_zero (Or.inl (by push_cast; omega)), Matrix.mul_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

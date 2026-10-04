import CORALean.ContDynamics.LinearARX.Operations.Btilde

/-!
# One more step of the input parameters

`B̃ᵢ(k+1) = B̄_ext,i + Ā_ext B̃ᵢ₋₁(k)`: peel the `j = 0` term off (9b) and factor
`Ā_ext` out of the rest. This is the recursion (11) unrolls into, and the induction step
behind [1, Thm. 1] and [1, Lemma 1].

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

theorem LinearARX.Btilde_succ (sys : LinearARX 𝕋 dy du p) (k : ℕ) (i : ℤ) :
    sys.Btilde (k + 1) i = sys.Bext i + sys.Aext * sys.Btilde k (i - 1) := by -- --- PROOF ---
  unfold LinearARX.Btilde
  rw [Finset.sum_range_succ', Matrix.mul_sum, add_comm]
  congr 1
  · rw [pow_zero, Matrix.one_mul, Nat.cast_zero, sub_zero]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ', Matrix.mul_assoc]
    congr 2
    push_cast
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

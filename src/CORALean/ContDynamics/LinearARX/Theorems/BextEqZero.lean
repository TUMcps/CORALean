import CORALean.ContDynamics.LinearARX.Operations.Bext

/-!
# The extended input matrices vanish outside the lags

`B̄_ext,i = 0` for `i < 0` and `i > p`, as [1] reads it below Eq. 10: the convention
every reindexing of (9b) in [1, Thm. 1] leans on.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.Bext_eq_zero (sys : LinearARX 𝕋 dy du p) {i : ℤ} (hi : i < 0 ∨ (p : ℤ) < i) :
    sys.Bext i = 0 := by
  unfold LinearARX.Bext
  rw [dif_neg (by omega)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

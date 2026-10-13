import CORALean.ContDynamics.LinearSys.Operations.InputTerm

/-!
# Orders `1` through `η` of the input solution, summed

[1, Alg. 2] line 16's `P̂^U_∞(Δt_k)` half of eq. (27): `LinearSys.inputTaylorSum`
starting at order `1` rather than `0`, since order `0` is the separate
`P̂^U_0(Δt_k) = Δt_k·U₀` that line 18 accumulates instead. Below order `1` the sum is empty,
matched by the zero matrix, whose image `{0}` is what an empty sum denotes.

Recursive rather than a fold over `Finset`, for the reason `inputTaylorSum`
gives: `plus` is only an enclosure and never has to be reassociated.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Inner- and Outer-Approximations of
      Reachable Sets". IEEE Transactions on Automatic Control, vol. 68, no. 12,
      2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Orders `1 … η` of the input solution, `0` below order `1`. -/
noncomputable def LinearSys.inputTaylorSumTail (sys : LinearSys 𝕋 n) (r : ℝ) (U : S n) :
    ℕ → S n
  | 0 => Mtimes.mtimes (0 : Mat ℝ n n) U
  | 1 => Mtimes.mtimes (sys.inputTerm r 1) U
  | i + 2 => Plus.plus (sys.inputTaylorSumTail r U (i + 1))
      (Mtimes.mtimes (sys.inputTerm r (i + 2)) U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

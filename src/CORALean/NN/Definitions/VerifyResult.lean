module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The verdict of the set-based verification

[1, Alg. 1]'s output, `VERIFIED` or `FALSIFIED(x̃)` with a counterexample `x̃`, and the verdict
CORA's `neuralNetwork/verify` returns when it stops at `options.nn.max_verif_iter` or the
timeout with the queue still holding sets, `UNKNOWN`; the printed loop has no such bound.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- `VERIFIED`, `FALSIFIED(x̃)` with a counterexample, or `UNKNOWN` when the budget runs out. -/
inductive SetBasedNet.VerifyResult (n : ℕ) where
  | verified
  | falsified (x : Vec ℝ n)
  | unknown

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

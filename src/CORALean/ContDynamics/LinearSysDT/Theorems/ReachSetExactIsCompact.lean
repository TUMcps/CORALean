module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSetExact
public import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section

/-!
# `reachSetExact` is compact

Induction on `k`, the step being a linear image — continuous, `Vec ℝ n` being
finite-dimensional, so `IsCompact.image` carries it — summed with `construct U`
by `IsCompact.add`. Compactness rather than closedness: a sum of two closed sets
need not be closed, so closedness alone would not survive the step, while a sum
of two compact sets is compact.

The other missing hypothesis `minkowskiDiff_inner_of_outer` asks of the exact
set; `ReachSetExactConvex` supplies convexity.

## Inputs
* `sys` – system
* `R₀` – initial set
* `U` – input set
* `k` – step

## Hypotheses
* `hR₀` – initial set compact
* `hU` – input set compact

## Conclusion
* the exact reachable set is compact
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exact set reached in `k` steps is compact whenever the initial and input
sets are. -/
theorem LinearSysDT.reachSetExact_isCompact (sys : LinearSysDT 𝕋 n) {R₀ U : S n}
    (hR₀ : IsCompact (construct R₀)) (hU : IsCompact (construct U)) (k : ℕ) : -- --- CONCL ---
    IsCompact (sys.reachSetExact R₀ U k) := by -- --- PROOF ---
  induction k with
  | zero => exact hR₀
  | succ k ih =>
    show IsCompact (mulVecLin (toRealMat sys.A) '' sys.reachSetExact R₀ U k + construct U)
    exact (ih.image (mulVecLin (toRealMat sys.A)).continuous_of_finiteDimensional).add hU

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

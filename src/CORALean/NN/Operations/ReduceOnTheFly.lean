module

public import CORALean.NN.Operations.ReduceOnTheFlyFrom

@[expose] public section

/-!
# [1, Alg. 2]: reducing a network on the fly

[1, Alg. 2] walks the nonlinear layers `k = 2, 4, …, κ` of a `ReducibleNetwork`, reducing
each against the set that actually reaches it, and returns the reduced network `Φ̂_ρ` with
the output set `Y = H_κ` it computed on the way. Written once over the scalar: at a machine
scalar it runs, the look-ahead boxes and [1, Prop. 4]'s error boxes rounding outward.

`reduceOnTheFly_outer` is its soundness at every instance of the network, and
`Real.reduceOnTheFly_reducesAt` puts what it returns at `𝕋 := ℝ` in `ReducesAt`.

## Inputs
* `le` – comparison of two scalars
* `tol` – tolerance on the remaining fraction
* `fuel` – bound on the loop iterations
* `n` – input width
* `m` – output width
* `X` – input set
* `ρ` – reduction rate

## Output
* reduced network and the output set computed on the way, or none if the fuel runs out

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float ContSet IntervalOuter

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the network `Φ` reduced at rate `ρ` along the input set `X`, and the output
set `Y` it computes on the way; `none` where [1, Alg. 1] ran out of `fuel` at some layer. -/
def reduceOnTheFly (le : 𝕋 → 𝕋 → Bool) (tol : 𝕋) (fuel : ℕ) {n m : ℕ} (X : S n) (ρ : 𝕋) :
    ReducibleNetwork 𝕋 n m → Option (ReducibleNetwork 𝕋 n m × S m)
  -- 2. `for k = 2, 4, …, κ`, empty for `κ = 0`: nothing to reduce, `Y ← H_0`
  | .nil => some (.nil, X)
  | .cons L_1 L_2 hσ B rest =>
    -- 1. `H_0 ← X`
    let H_0 := X
    -- 1. `L̂_1 ← L_1`
    let Lhat_1 := L_1
    -- 2. `for k = 2, 4, …, κ` (lines 3-12), then 13. `return Y ← H_κ`
    reduceOnTheFlyFrom le tol fuel ρ H_0 Lhat_1 L_2 hσ B rest

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

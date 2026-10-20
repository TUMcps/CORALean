module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# The states some admissible input drives into the target

Backward reachability, in the `∃` reading: `x` is in the `k`-step set when *some* input signal `U`
admits carries it into `T` at step `k`. The `∀` reading is `backReachSetForallExact`, beside this
one and never in place of it. Written as the property itself, one existential per step, rather
than through an operation on sets. `Theorems.BackReachSetExistsExactPreimage` is the other face of
it: the preimage under `A` of a *Minkowski sum* with `-U`. Like `reachSetExact` this names no
operation class and nothing may widen it. `Theorems.BackReachSetExistsExactIsTrajectory` builds
the run the name promises; `Theorems.BackReachExistsOuter` puts a computed set around it.

## Inputs
* `sys` – system
* `T` – target set
* `U` – input set

## Output
* the states some input signal drives into the target in `k` steps
-/

-- Authors:       Claude Sonnet 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state from which *some* admissible input signal reaches `T` in
exactly `k` steps: one choice of input per step, and the state it produces is
where the remaining `k` steps start. -/
def LinearSysDT.backReachSetExistsExact (sys : LinearSysDT 𝕋 n) (T U : S n) : ℕ → Set (Vec ℝ n)
  | 0 => construct T
  | k + 1 => {x | ∃ u ∈ construct U,
      toRealMat sys.A *ᵥ x + u ∈ sys.backReachSetExistsExact T U k}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

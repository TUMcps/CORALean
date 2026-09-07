import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# The states some admissible input drives into the target

Backward reachability, in the `∃` reading: `x` is in the `k`-step set when
*some* input signal `U` admits carries it into `T` at step `k`. The `∀` reading
— every signal does — is `backReachSetForall`, beside this one and never in
place of it.

Written as the property itself, one existential per step, rather than through an
operation on sets. `Theorems.BackReachSetExistsPreimage` is the other face of
it: the preimage under `A` of a *Minkowski sum* with `-U`, which is where the
asymmetry with the `∀` reading sits — a sum is what `Plus` computes, outer,
while a difference is a guarantee and only ever inner.

Like `reachSet` and `backReachSetForall` this names no operation class and
nothing may widen it. `Theorems.BackReachSetExistsTrajectory` builds the run the
name promises; `Theorems.BackReachExistsOuter` puts a computed set around it.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state from which *some* admissible input signal reaches `T` in
exactly `k` steps: one choice of input per step, and the state it produces is
where the remaining `k` steps start. -/
def LinearSysDT.backReachSetExists (sys : LinearSysDT 𝕋 n) (T U : S n) : ℕ → Set (Vec ℝ n)
  | 0 => construct T
  | k + 1 => {x | ∃ u ∈ construct U,
      toRealMat sys.A *ᵥ x + u ∈ sys.backReachSetExists T U k}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

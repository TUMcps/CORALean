module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# The states every admissible input drives into the target

Backward reachability, in the `∀` reading: `x` is in the `k`-step set when
*every* input signal `U` admits carries it into `T` at step `k`. The `∃`
reading — *some* signal does — is a different set: `backReachSetExists`, beside
this one and never in place of it.

The `∀` reading is what a Minkowski difference computes, which is why one was
the prerequisite: `{x | ∀ u ∈ U, A x + u ∈ B}` is the preimage under `A` of
`B ⊖ U`. That is `reachSet`'s image and sum, each read backwards, and like
`reachSet` it names no operation class and nothing may widen it.

A preimage rather than an image under `A⁻¹`: this asks nothing of `A` at all,
and producing an inverse is the computed version's problem, not this one's.

`Theorems.BackReachSetForallIsTrajectory` proves what the name claims, against
the dynamics; `Theorems.BackReachForallInner` puts a computed set inside it.
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

/-- Every state from which *every* admissible input signal reaches `T` in
exactly `k` steps: one preimage and one Minkowski difference per step. -/
def LinearSysDT.backReachSetForall (sys : LinearSysDT 𝕋 n) (T U : S n) : ℕ → Set (Vec ℝ n)
  | 0 => construct T
  | k + 1 => mulVecLin (toRealMat sys.A) ⁻¹'
      minkowskiDiff (sys.backReachSetForall T U k) (construct U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContDynamics.LinearSysDT.Definitions.ReachParams
import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSetOfInit

/-!
# The exact set `Reach LinearSysDT.WithInput` is asked to enclose

Every state reachable in at most `K` steps from a bare initial set, `K` from
`Reach`'s `Params` — the `Reach.reachExact` field of the instance.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in at most `p.K` steps from a bare initial set `X`. -/
def LinearSysDT.WithInput.reachUnionExact (sys : LinearSysDT.WithInput 𝕋 S n)
    (p : LinearSysDT.ReachParams) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ k ≤ p.K, sys.reachSetOfInit X k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

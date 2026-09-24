import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachParams
import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachSetOfInit

/-!
# The exact set `Reach LinParamSysDT.WithInput` is asked to enclose

Every state reachable in at most `K` steps from a bare initial set, `K` from
`Reach.Params` — the `Reach.reachExact` field of the instance.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in at most `p.K` steps from a bare initial set `X`. -/
def LinParamSysDT.WithInput.reachUnionExact (sys : LinParamSysDT.WithInput 𝕄 S n)
    (p : LinParamSysDT.ReachParams) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ k ≤ p.K, sys.reachSetOfInit X k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
